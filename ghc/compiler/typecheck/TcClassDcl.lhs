%
% (c) The GRASP/AQUA Project, Glasgow University, 1992-1998
%
\section[TcClassDcl]{Typechecking class declarations}

\begin{code}
module TcClassDcl ( tcClassDecl1, checkValidClass, tcClassDecls2, 
		    tcMethodBind, badMethodErr
		  ) where

#include "HsVersions.h"

import HsSyn		( TyClDecl(..), Sig(..), MonoBinds(..),
			  HsExpr(..), HsLit(..), 
			  mkSimpleMatch, andMonoBinds, andMonoBindList, 
			  isClassOpSig, isPragSig,
			  getClassDeclSysNames, placeHolderType
			)
import BasicTypes	( TopLevelFlag(..), RecFlag(..), StrictnessMark(..) )
import RnHsSyn		( RenamedTyClDecl, 
			  RenamedClassOpSig, RenamedMonoBinds,
			  RenamedSig, maybeGenericMatch
			)
import TcHsSyn		( TcMonoBinds )

import Inst		( Inst, InstOrigin(..), LIE, emptyLIE, plusLIE, plusLIEs, 
			  instToId, newDicts, newMethod )
import TcEnv		( RecTcEnv, TyThingDetails(..), 
			  tcLookupClass, tcExtendTyVarEnvForMeths, tcExtendGlobalTyVars,
			  tcExtendLocalValEnv, tcExtendTyVarEnv
			)
import TcBinds		( tcBindWithSigs, tcSpecSigs )
import TcMonoType	( tcHsType, tcHsTheta, mkTcSig )
import TcSimplify	( tcSimplifyCheck, bindInstsOfLocalFuns )
import TcUnify		( checkSigTyVars, sigCtxt )
import TcMType		( tcInstSigTyVars, checkValidTheta, checkValidType, SourceTyCtxt(..), UserTypeCtxt(..) )
import TcType		( Type, TyVarDetails(..), TcType, TcThetaType, TcTyVar, 
			  mkTyVarTys, mkPredTys, mkClassPred, 
			  tcIsTyVarTy, tcSplitTyConApp_maybe, tcSplitSigmaTy
			)
import TcMonad
import Generics		( mkGenericRhs, validGenericMethodType )
import PrelInfo		( nO_METHOD_BINDING_ERROR_ID )
import Class		( classTyVars, classBigSig, classTyCon, className,
			  Class, ClassOpItem, DefMeth (..) )
import MkId		( mkDictSelId, mkDataConId, mkDataConWrapId, mkDefaultMethodId )
import DataCon		( mkDataCon )
import Id		( Id, idType, idName, setIdLocalExported )
import Module		( Module )
import Name		( Name, NamedThing(..) )
import NameEnv		( NameEnv, lookupNameEnv, emptyNameEnv, unitNameEnv, plusNameEnv )
import NameSet		( emptyNameSet )
import Outputable
import Var		( TyVar )
import VarSet		( mkVarSet, emptyVarSet )
import CmdLineOpts
import ErrUtils		( dumpIfSet )
import Util		( count, isSingleton, lengthIs, equalLength )
import Maybes		( seqMaybe, maybeToBool )
\end{code}



Dictionary handling
~~~~~~~~~~~~~~~~~~~
Every class implicitly declares a new data type, corresponding to dictionaries
of that class. So, for example:

	class (D a) => C a where
	  op1 :: a -> a
	  op2 :: forall b. Ord b => a -> b -> b

would implicitly declare

	data CDict a = CDict (D a)	
			     (a -> a)
			     (forall b. Ord b => a -> b -> b)

(We could use a record decl, but that means changing more of the existing apparatus.
One step at at time!)

For classes with just one superclass+method, we use a newtype decl instead:

	class C a where
	  op :: forallb. a -> b -> b

generates

	newtype CDict a = CDict (forall b. a -> b -> b)

Now DictTy in Type is just a form of type synomym: 
	DictTy c t = TyConTy CDict `AppTy` t

Death to "ExpandingDicts".


%************************************************************************
%*									*
\subsection{Type checking}
%*									*
%************************************************************************

\begin{code}

tcClassDecl1 :: RenamedTyClDecl -> TcM (Name, TyThingDetails)
tcClassDecl1 (ClassDecl {tcdCtxt = context, tcdName = class_name,
			 tcdTyVars = tyvar_names, tcdFDs = fundeps,
			 tcdSigs = class_sigs, tcdMeths = def_methods,
			 tcdSysNames = sys_names, tcdLoc = src_loc})
  = 	-- LOOK THINGS UP IN THE ENVIRONMENT
    tcLookupClass class_name				`thenTc` \ clas ->
    let
	tyvars   = classTyVars clas
	op_sigs  = filter isClassOpSig class_sigs
	op_names = [n | ClassOpSig n _ _ _ <- op_sigs]
	(_, datacon_name, datacon_wkr_name, sc_sel_names) = getClassDeclSysNames sys_names
    in
    tcExtendTyVarEnv tyvars				$ 

    checkDefaultBinds clas op_names def_methods	  `thenTc` \ mb_dm_env ->
	
	-- CHECK THE CONTEXT
	-- The renamer has already checked that the context mentions
	-- only the type variable of the class decl.
	-- Context is already kind-checked
    ASSERT( equalLength context sc_sel_names )
    tcHsTheta context					`thenTc` \ sc_theta ->

	-- CHECK THE CLASS SIGNATURES,
    mapTc (tcClassSig clas tyvars mb_dm_env) op_sigs	`thenTc` \ sig_stuff ->

	-- MAKE THE CLASS DETAILS
    let
	(op_tys, op_items) = unzip sig_stuff
        sc_tys		   = mkPredTys sc_theta
	dict_component_tys = sc_tys ++ op_tys
        sc_sel_ids	   = [mkDictSelId sc_name clas | sc_name <- sc_sel_names]

        dict_con = mkDataCon datacon_name
			     [NotMarkedStrict | _ <- dict_component_tys]
			     [{- No labelled fields -}]
		      	     tyvars
		      	     [{-No context-}]
			     [{-No existential tyvars-}] [{-Or context-}]
			     dict_component_tys
		      	     (classTyCon clas)
			     dict_con_id dict_wrap_id

	dict_con_id  = mkDataConId datacon_wkr_name dict_con
	dict_wrap_id = mkDataConWrapId dict_con
    in
    returnTc (class_name, ClassDetails sc_theta sc_sel_ids op_items dict_con)
\end{code}

\begin{code}
checkDefaultBinds :: Class -> [Name] -> Maybe RenamedMonoBinds
		  -> TcM (Maybe (NameEnv Bool))
	-- The returned environment says
	--	x not in env => no default method
	--	x -> True    => generic default method
	--	x -> False   => polymorphic default method

  -- Check default bindings
  -- 	a) must be for a class op for this class
  --	b) must be all generic or all non-generic
  -- and return a mapping from class-op to DefMeth info

  -- But do all this only for source binds

checkDefaultBinds clas ops Nothing
  = returnTc Nothing

checkDefaultBinds clas ops (Just mbs)
  = go mbs	`thenTc` \ dm_env ->
    returnTc (Just dm_env)
  where
    go EmptyMonoBinds = returnTc emptyNameEnv

    go (AndMonoBinds b1 b2)
      = go b1	`thenTc` \ dm_info1 ->
        go b2	`thenTc` \ dm_info2 ->
        returnTc (dm_info1 `plusNameEnv` dm_info2)

    go (FunMonoBind op _ matches loc)
      = tcAddSrcLoc loc					$

  	-- Check that the op is from this class
	checkTc (op `elem` ops) (badMethodErr clas op)		`thenTc_`

   	-- Check that all the defns ar generic, or none are
	checkTc (all_generic || none_generic) (mixedGenericErr op)	`thenTc_`

	returnTc (unitNameEnv op all_generic)
      where
	n_generic    = count (maybeToBool . maybeGenericMatch) matches
	none_generic = n_generic == 0
	all_generic  = matches `lengthIs` n_generic
\end{code}


\begin{code}
tcClassSig :: Class	    		-- ...ditto...
	   -> [TyVar]		 	-- The class type variable, used for error check only
	   -> Maybe (NameEnv Bool)	-- Info about default methods; 
					--	Nothing => imported class defn with no method binds
	   -> RenamedClassOpSig
	   -> TcM (Type,		-- Type of the method
		     ClassOpItem)	-- Selector Id, default-method Id, True if explicit default binding

-- This warrants an explanation: we need to separate generic
-- default methods and default methods later on in the compiler
-- so we distinguish them in checkDefaultBinds, and pass this knowledge in the
-- Class.DefMeth data structure. 

tcClassSig clas clas_tyvars maybe_dm_env
	   (ClassOpSig op_name sig_dm op_ty src_loc)
  = tcAddSrcLoc src_loc $

	-- Check the type signature.  NB that the envt *already has*
	-- bindings for the type variables; see comments in TcTyAndClassDcls.
    tcHsType op_ty			`thenTc` \ local_ty ->

    let
	theta = [mkClassPred clas (mkTyVarTys clas_tyvars)]

	-- Build the selector id and default method id
	sel_id = mkDictSelId op_name clas
	DefMeth dm_name = sig_dm

	dm_info = case maybe_dm_env of
		    Nothing     -> sig_dm
		    Just dm_env -> mk_src_dm_info dm_env

	mk_src_dm_info dm_env = case lookupNameEnv dm_env op_name of
				   Nothing    -> NoDefMeth
				   Just True  -> GenDefMeth
				   Just False -> DefMeth dm_name
    in
    returnTc (local_ty, (sel_id, dm_info))
\end{code}

checkValidClass is called once the mutually-recursive knot has been
tied, so we can look at things freely.

\begin{code}
checkValidClass :: Class -> TcM ()
checkValidClass cls
  = 	-- CHECK ARITY 1 FOR HASKELL 1.4
    doptsTc Opt_GlasgowExts				`thenTc` \ gla_exts ->

    	-- Check that the class is unary, unless GlaExs
    checkTc (not (null tyvars))		(nullaryClassErr cls)	`thenTc_`
    checkTc (gla_exts || unary) (classArityErr cls)	`thenTc_`

   	-- Check the super-classes
    checkValidTheta (ClassSCCtxt (className cls)) theta	`thenTc_`

	-- Check the class operations
    mapTc_ check_op op_stuff		`thenTc_`

  	-- Check that if the class has generic methods, then the
	-- class has only one parameter.  We can't do generic
	-- multi-parameter type classes!
    checkTc (unary || no_generics) (genericMultiParamErr cls)

  where
    (tyvars, theta, _, op_stuff) = classBigSig cls
    unary 	= isSingleton tyvars
    no_generics = null [() | (_, GenDefMeth) <- op_stuff]

    check_op (sel_id, dm) 
	= checkValidTheta SigmaCtxt (tail theta) 	`thenTc_`
		-- The 'tail' removes the initial (C a) from the
		-- class itself, leaving just the method type

	  checkValidType (FunSigCtxt op_name) tau	`thenTc_`

		-- Check that for a generic method, the type of 
		-- the method is sufficiently simple
	  checkTc (dm /= GenDefMeth || validGenericMethodType op_ty)
		  (badGenericMethodType op_name op_ty)
	where
	  op_name = idName sel_id
	  op_ty   = idType sel_id
	  (_,theta,tau) = tcSplitSigmaTy op_ty
\end{code}


%************************************************************************
%*									*
\subsection[Default methods]{Default methods}
%*									*
%************************************************************************

The default methods for a class are each passed a dictionary for the
class, so that they get access to the other methods at the same type.
So, given the class decl
\begin{verbatim}
class Foo a where
	op1 :: a -> Bool
	op2 :: Ord b => a -> b -> b -> b

	op1 x = True
	op2 x y z = if (op1 x) && (y < z) then y else z
\end{verbatim}
we get the default methods:
\begin{verbatim}
defm.Foo.op1 :: forall a. Foo a => a -> Bool
defm.Foo.op1 = /\a -> \dfoo -> \x -> True

defm.Foo.op2 :: forall a. Foo a => forall b. Ord b => a -> b -> b -> b
defm.Foo.op2 = /\ a -> \ dfoo -> /\ b -> \ dord -> \x y z ->
		  if (op1 a dfoo x) && (< b dord y z) then y else z
\end{verbatim}

When we come across an instance decl, we may need to use the default
methods:
\begin{verbatim}
instance Foo Int where {}
\end{verbatim}
gives
\begin{verbatim}
const.Foo.Int.op1 :: Int -> Bool
const.Foo.Int.op1 = defm.Foo.op1 Int dfun.Foo.Int

const.Foo.Int.op2 :: forall b. Ord b => Int -> b -> b -> b
const.Foo.Int.op2 = defm.Foo.op2 Int dfun.Foo.Int

dfun.Foo.Int :: Foo Int
dfun.Foo.Int = (const.Foo.Int.op1, const.Foo.Int.op2)
\end{verbatim}
Notice that, as with method selectors above, we assume that dictionary
application is curried, so there's no need to mention the Ord dictionary
in const.Foo.Int.op2 (or the type variable).

\begin{verbatim}
instance Foo a => Foo [a] where {}

dfun.Foo.List :: forall a. Foo a -> Foo [a]
dfun.Foo.List
  = /\ a -> \ dfoo_a ->
    let rec
	op1 = defm.Foo.op1 [a] dfoo_list
	op2 = defm.Foo.op2 [a] dfoo_list
	dfoo_list = (op1, op2)
    in
	dfoo_list
\end{verbatim}

The function @tcClassDecls2@ just arranges to apply @tcClassDecl2@ to
each local class decl.

\begin{code}
tcClassDecls2 :: Module -> [RenamedTyClDecl] -> NF_TcM (LIE, TcMonoBinds, [Id])

tcClassDecls2 this_mod decls
  = foldr combine
	  (returnNF_Tc (emptyLIE, EmptyMonoBinds, []))
	  [tcClassDecl2 cls_decl | cls_decl@(ClassDecl {tcdMeths = Just _}) <- decls] 
		-- The 'Just' picks out source ClassDecls
  where
    combine tc1 tc2 = tc1 `thenNF_Tc` \ (lie1, binds1, ids1) ->
		      tc2 `thenNF_Tc` \ (lie2, binds2, ids2) ->
		      returnNF_Tc (lie1 `plusLIE` lie2,
				   binds1 `AndMonoBinds` binds2,
				   ids1 ++ ids2)
\end{code}

@tcClassDecl2@ generates bindings for polymorphic default methods
(generic default methods have by now turned into instance declarations)

\begin{code}
tcClassDecl2 :: RenamedTyClDecl		-- The class declaration
	     -> NF_TcM (LIE, TcMonoBinds, [Id])

tcClassDecl2 (ClassDecl {tcdName = class_name, tcdSigs = sigs, 
			 tcdMeths = Just default_binds, tcdLoc = src_loc})
  = 	-- The 'Just' picks out source ClassDecls
    recoverNF_Tc (returnNF_Tc (emptyLIE, EmptyMonoBinds, [])) $ 
    tcAddSrcLoc src_loc		     		          $
    tcLookupClass class_name				  `thenNF_Tc` \ clas ->

	-- We make a separate binding for each default method.
	-- At one time I used a single AbsBinds for all of them, thus
	-- AbsBind [d] [dm1, dm2, dm3] { dm1 = ...; dm2 = ...; dm3 = ... }
	-- But that desugars into
	--	ds = \d -> (..., ..., ...)
	--	dm1 = \d -> case ds d of (a,b,c) -> a
	-- And since ds is big, it doesn't get inlined, so we don't get good
	-- default methods.  Better to make separate AbsBinds for each
    let
	(tyvars, _, _, op_items) = classBigSig clas
	prags 			 = filter isPragSig sigs
	tc_dm			 = tcDefMeth clas tyvars default_binds prags
    in
    mapAndUnzip3Tc tc_dm op_items	`thenTc` \ (defm_binds, const_lies, dm_ids_s) ->

    returnTc (plusLIEs const_lies, andMonoBindList defm_binds, concat dm_ids_s)
    

tcDefMeth clas tyvars binds_in prags (_, NoDefMeth)  = returnTc (EmptyMonoBinds, emptyLIE, [])
tcDefMeth clas tyvars binds_in prags (_, GenDefMeth) = returnTc (EmptyMonoBinds, emptyLIE, [])
	-- Generate code for polymorphic default methods only
	-- (Generic default methods have turned into instance decls by now.)
	-- This is incompatible with Hugs, which expects a polymorphic 
	-- default method for every class op, regardless of whether or not 
	-- the programmer supplied an explicit default decl for the class.  
	-- (If necessary we can fix that, but we don't have a convenient Id to hand.)

tcDefMeth clas tyvars binds_in prags op_item@(sel_id, DefMeth dm_name)
  = tcInstSigTyVars ClsTv tyvars			`thenNF_Tc` \ clas_tyvars ->
    let
	dm_ty = idType sel_id	-- Same as dict selector!
          -- The default method's type should really come from the
          -- iface file, since it could be usage-generalised, but this
          -- requires altering the mess of knots in TcModule and I'm
          -- too scared to do that.  Instead, I have disabled generalisation
          -- of types of default methods (and dict funs) by annotating them
          -- TyGenNever (in MkId).  Ugh!  KSW 1999-09.

	inst_tys    = mkTyVarTys clas_tyvars
        theta       = [mkClassPred clas inst_tys]
 	dm_id       = mkDefaultMethodId dm_name dm_ty
	local_dm_id = setIdLocalExported dm_id
		-- Reason for setIdLocalExported: see notes with MkId.mkDictFunId
    in
    newDicts origin theta 		`thenNF_Tc` \ [this_dict] ->

    tcExtendTyVarEnvForMeths tyvars clas_tyvars (
        tcMethodBind clas origin clas_tyvars inst_tys theta
	             binds_in prags False op_item
    )					`thenTc` \ (defm_bind, insts_needed, local_dm_inst) ->
    
    tcAddErrCtxt (defltMethCtxt clas) $
    
        -- Check the context
    tcSimplifyCheck
        (ptext SLIT("class") <+> ppr clas)
	clas_tyvars
        [this_dict]
        insts_needed				`thenTc` \ (const_lie, dict_binds) ->

	-- Simplification can do unification
    checkSigTyVars clas_tyvars emptyVarSet	`thenTc` \ clas_tyvars' ->
    
    let
        full_bind = AbsBinds
    		    clas_tyvars'
    		    [instToId this_dict]
    		    [(clas_tyvars', local_dm_id, instToId local_dm_inst)]
    		    emptyNameSet	-- No inlines (yet)
    		    (dict_binds `andMonoBinds` defm_bind)
    in
    returnTc (full_bind, const_lie, [dm_id])
  where
    origin = ClassDeclOrigin
\end{code}

    

%************************************************************************
%*									*
\subsection{Typechecking a method}
%*									*
%************************************************************************

@tcMethodBind@ is used to type-check both default-method and
instance-decl method declarations.  We must type-check methods one at a
time, because their signatures may have different contexts and
tyvar sets.

\begin{code}
tcMethodBind 
	:: Class
	-> InstOrigin
	-> [TcTyVar]		-- Instantiated type variables for the
				--  enclosing class/instance decl. 
				--  They'll be signature tyvars, and we
				--  want to check that they don't get bound
	-> [TcType]		-- Instance types
	-> TcThetaType		-- Available theta; this could be used to check
				--  the method signature, but actually that's done by
				--  the caller;  here, it's just used for the error message
	-> RenamedMonoBinds	-- Method binding (pick the right one from in here)
	-> [RenamedSig]		-- Pramgas (just for this one)
	-> Bool			-- True <=> This method is from an instance declaration
	-> ClassOpItem		-- The method selector and default-method Id
	-> TcM (TcMonoBinds, LIE, Inst)

tcMethodBind clas origin inst_tyvars inst_tys inst_theta
	     meth_binds prags is_inst_decl (sel_id, dm_info)
  = tcGetSrcLoc 			`thenNF_Tc` \ loc -> 
    newMethod origin sel_id inst_tys	`thenNF_Tc` \ meth ->
    let
	meth_id	   = instToId meth
	meth_name  = idName meth_id
	meth_prags = find_prags (idName sel_id) meth_name prags
    in
    mkTcSig meth_id loc			`thenNF_Tc` \ sig_info -> 

	-- Figure out what method binding to use
	-- If the user suppplied one, use it, else construct a default one
    (case find_bind (idName sel_id) meth_name meth_binds of
	Just user_bind -> returnTc user_bind 
	Nothing	       -> mkDefMethRhs is_inst_decl clas inst_tys sel_id loc dm_info	`thenTc` \ rhs ->
			  returnTc (FunMonoBind meth_name False	-- Not infix decl
				                [mkSimpleMatch [] rhs placeHolderType loc] loc)
    )								`thenTc` \ meth_bind ->
     -- Check the bindings; first add inst_tyvars to the envt
     -- so that we don't quantify over them in nested places
     -- The *caller* put the class/inst decl tyvars into the envt
     tcExtendGlobalTyVars (mkVarSet inst_tyvars) 
     		    (tcAddErrCtxt (methodCtxt sel_id)		$
     		     tcBindWithSigs NotTopLevel meth_bind 
		   		    [sig_info] meth_prags NonRecursive 
     		    ) 						`thenTc` \ (binds, insts, _) -> 

     tcExtendLocalValEnv [(meth_name, meth_id)] 
			 (tcSpecSigs meth_prags)		`thenTc` \ (prag_binds1, prag_lie) ->
     
     -- The prag_lie for a SPECIALISE pragma will mention the function
     -- itself, so we have to simplify them away right now lest they float
     -- outwards!
     bindInstsOfLocalFuns prag_lie [meth_id]	`thenTc` \ (prag_lie', prag_binds2) ->

     -- Now check that the instance type variables
     -- (or, in the case of a class decl, the class tyvars)
     -- have not been unified with anything in the environment
     --	
     -- We do this for each method independently to localise error messages
     -- ...and this is why the call to tcExtendGlobalTyVars must be here
     --    rather than in the caller
     tcAddErrCtxt (ptext SLIT("When checking the type of class method") 
		   <+> quotes (ppr sel_id))					$
     tcAddErrCtxtM (sigCtxt inst_tyvars inst_theta (idType meth_id))	$
     checkSigTyVars inst_tyvars emptyVarSet					`thenTc_` 

     returnTc (binds `AndMonoBinds` prag_binds1 `AndMonoBinds` prag_binds2, 
	       insts `plusLIE` prag_lie',
	       meth)

     -- The user didn't supply a method binding, 
     -- so we have to make up a default binding
     -- The RHS of a default method depends on the default-method info
mkDefMethRhs is_inst_decl clas inst_tys sel_id loc (DefMeth dm_name)
  =  -- An polymorphic default method
    returnTc (HsVar dm_name)

mkDefMethRhs is_inst_decl clas inst_tys sel_id loc NoDefMeth
  =  	-- No default method
	-- Warn only if -fwarn-missing-methods
    doptsTc Opt_WarnMissingMethods 		`thenNF_Tc` \ warn -> 
    warnTc (is_inst_decl && warn)
   	   (omittedMethodWarn sel_id)		`thenNF_Tc_`
    returnTc error_rhs
  where
    error_rhs = HsApp (HsVar (getName nO_METHOD_BINDING_ERROR_ID)) 
	    		  (HsLit (HsString (_PK_ error_msg)))
    error_msg = showSDoc (hcat [ppr loc, text "|", ppr sel_id ])


mkDefMethRhs is_inst_decl clas inst_tys sel_id loc GenDefMeth 
  =  	-- A generic default method
	-- If the method is defined generically, we can only do the job if the
	-- instance declaration is for a single-parameter type class with
	-- a type constructor applied to type arguments in the instance decl
	-- 	(checkTc, so False provokes the error)
     checkTc (not is_inst_decl || simple_inst)
	     (badGenericInstance sel_id)			`thenTc_`

     ioToTc (dumpIfSet opt_PprStyle_Debug "Generic RHS" stuff)	`thenNF_Tc_`
     returnTc rhs
  where
    rhs = mkGenericRhs sel_id clas_tyvar tycon

    stuff = vcat [ppr clas <+> ppr inst_tys,
		  nest 4 (ppr sel_id <+> equals <+> ppr rhs)]

	  -- The tycon is only used in the generic case, and in that
	  -- case we require that the instance decl is for a single-parameter
	  -- type class with type variable arguments:
	  --	instance (...) => C (T a b)
    simple_inst   = maybeToBool maybe_tycon
    clas_tyvar    = head (classTyVars clas)
    Just tycon	  = maybe_tycon
    maybe_tycon   = case inst_tys of 
			[ty] -> case tcSplitTyConApp_maybe ty of
				  Just (tycon, arg_tys) | all tcIsTyVarTy arg_tys -> Just tycon
				  other						  -> Nothing
			other -> Nothing
\end{code}


\begin{code}
-- The renamer just puts the selector ID as the binder in the method binding
-- but we must use the method name; so we substitute it here.  Crude but simple.
find_bind sel_name meth_name (FunMonoBind op_name fix matches loc)
    | op_name == sel_name = Just (FunMonoBind meth_name fix matches loc)
find_bind sel_name meth_name (AndMonoBinds b1 b2)
    = find_bind sel_name meth_name b1 `seqMaybe` find_bind sel_name meth_name b2
find_bind sel_name meth_name other  = Nothing	-- Default case

 -- Find the prags for this method, and replace the
 -- selector name with the method name
find_prags sel_name meth_name [] = []
find_prags sel_name meth_name (SpecSig name ty loc : prags) 
     | name == sel_name = SpecSig meth_name ty loc : find_prags sel_name meth_name prags
find_prags sel_name meth_name (InlineSig sense name phase loc : prags)
   | name == sel_name = InlineSig sense meth_name phase loc : find_prags sel_name meth_name prags
find_prags sel_name meth_name (prag:prags) = find_prags sel_name meth_name prags
\end{code}


Contexts and errors
~~~~~~~~~~~~~~~~~~~
\begin{code}
nullaryClassErr cls
  = ptext SLIT("No parameters for class")  <+> quotes (ppr cls)

classArityErr cls
  = vcat [ptext SLIT("Too many parameters for class") <+> quotes (ppr cls),
	  parens (ptext SLIT("Use -fglasgow-exts to allow multi-parameter classes"))]

defltMethCtxt clas
  = ptext SLIT("When checking the default methods for class") <+> quotes (ppr clas)

methodCtxt sel_id
  = ptext SLIT("In the definition for method") <+> quotes (ppr sel_id)

badMethodErr clas op
  = hsep [ptext SLIT("Class"), quotes (ppr clas), 
	  ptext SLIT("does not have a method"), quotes (ppr op)]

omittedMethodWarn sel_id
  = ptext SLIT("No explicit method nor default method for") <+> quotes (ppr sel_id)

badGenericMethodType op op_ty
  = hang (ptext SLIT("Generic method type is too complex"))
       4 (vcat [ppr op <+> dcolon <+> ppr op_ty,
		ptext SLIT("You can only use type variables, arrows, and tuples")])

badGenericInstance sel_id
  = sep [ptext SLIT("Can't derive generic code for") <+> quotes (ppr sel_id),
	 ptext SLIT("because the instance declaration is not for a simple type (T a b c)"),
	 ptext SLIT("(where T is a derivable type constructor)")]

mixedGenericErr op
  = ptext SLIT("Can't mix generic and non-generic equations for class method") <+> quotes (ppr op)

genericMultiParamErr clas
  = ptext SLIT("The multi-parameter class") <+> quotes (ppr clas) <+> 
    ptext SLIT("cannot have generic methods")
\end{code}
