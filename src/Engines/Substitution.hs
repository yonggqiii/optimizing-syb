module Engines.Substitution where
import GHC.Plugins

class Substitutable b c where
  substitute :: Var -> b -> c -> c

instance Substitutable b c => Substitutable b [c] where
  substitute a b = map (substitute a b)

{- Base: Var -> Var -> Var -> Var substitutions -}

instance Substitutable Var Var where
  substitute from to v 
    | from == v = to
      -- case of from and to not matching
    | isTyVar from && not (isTyVar to) = panic "impossible substitution of tyvar -> var"
    | not (isTyVar from) && isTyVar to = panic "impossible substitution of var -> tyvar"
      -- from :: TyVar, to :: TyVar, v :: Var
    | isTyVar from && not (isTyVar v) = updateVarType (substitute from to) v
      -- from :: Var, to :: Var, v :: Var
      -- from :: TyVar, to :: TyVar, v :: TyVar
      -- from :: Var, to :: Var, v :: TyVar
    | otherwise = v
  
{- Type-level substitutions -}
instance Substitutable Var Type where
  -- | Substitutes variables to variables in a type
  substitute from to t
      -- term-level substitution on a type; 
    | not (isTyVar from) || not (isTyVar to) = t -- panic "impossible substitution of term-level vars on a type"
      -- do ty_var -> ty_var -> ty_var substitution
    | isTyVarTy t = let t_var = getTypeVar t
                    in mkTyVarTy $ substitute from to t_var
    | isFunTy t   = let (mult_, lhs, rhs) = splitFunTy t
                        lhs' = substitute from to lhs
                        rhs' = substitute from to rhs
                    in  mkVisFunTy mult_ lhs' rhs'
    | isForAllTy t = let (lhs, rhs) = splitForAllTyVars t
                         lhs' = substitute from to lhs
                         rhs' = substitute from to rhs
                     in  mkSpecForAllTys lhs' rhs'
      -- perform substitution on all type arguments
    | otherwise   = let (tycon, ty_apps) = splitTyConApp t
                        new_ty_apps = substitute from to ty_apps
                    in  mkTyConApp tycon new_ty_apps

getTypeVar :: Type -> TyVar
getTypeVar = getTyVar "impossible! a definite type variable cant produce its type variable"

instance Substitutable Type Type where
  substitute from to t
      -- nothing to do because from is term-level
    | not (isTyVar from) = panic "impossible substitution of termvar -> Type"
      -- if to is a tyvar, deconstruct into tyvar -> tyvar -> type -> type
    | isTyVarTy to = let to_var = getTypeVar to
                     in substitute from to_var t
    | isTyVarTy t  = let t_var = getTypeVar t
                     in  if from == t_var then
                         to else
                         t
    | isFunTy t   = let (mult_, lhs, rhs) = splitFunTy t
                        lhs' = substitute from to lhs
                        rhs' = substitute from to rhs
                    in  mkVisFunTy mult_ lhs' rhs'
    | isForAllTy t = let (lhs, rhs) = splitForAllTyVars t
                         lhs' = substitute from to lhs
                         rhs' = substitute from to rhs
                     in  mkSpecForAllTys lhs' rhs'
  -- | Substitutes type variables to types in a type
    | otherwise   = let (tycon, ty_apps) = splitTyConApp t
                        new_ty_apps = substitute from to ty_apps
                    in  mkTyConApp tycon new_ty_apps

instance Substitutable Type Var where
  substitute from to v 
    | not (isTyVar from) = panic "impossible substitution of term-level var -> type"
      -- v is a tyvar, cannot produce Type, so must produce v itself
    | isTyVar v = v
      -- v is a term-level var, update its type
    | otherwise = updateVarType (substitute from to) v
 
instance Substitutable Type CoreExpr where
  substitute from _ _
    | not (isTyVar from) = panic "impossible substitution of term-level var -> type"
  substitute from to (Var v) = Var $ substitute from to v
  substitute _ _ (Lit l) = Lit l
  substitute from to (App f x) = App (substitute from to f) (substitute from to x)
  substitute from to (Lam b e) = Lam (substitute from to b) (substitute from to e)
  substitute from to (Let b e) = Let (substitute from to b) (substitute from to e)
  substitute from to (Case e b t alts) = Case (substitute from to e)
                                              (substitute from to b)
                                              (substitute from to t)
                                              (substitute from to alts)
  substitute from to (Cast b c) = Cast (substitute from to b) c
  substitute from to (Tick t e) = Tick t (substitute from to e)
  substitute from to (Type t) = Type (substitute from to t)
  substitute _ _ (Coercion c) = Coercion c
instance Substitutable Type (Alt Var) where
  substitute from _ _
    | not (isTyVar from) = panic "impossible substitution of term-level var -> type"
  substitute from to (Alt alt_con bs e) = Alt alt_con 
                                              (substitute from to bs)
                                              (substitute from to e)
instance Substitutable Type CoreBind where
  substitute from _ _
    | not (isTyVar from) = panic "impossible substitution of term-level var -> type"
  substitute from to (NonRec b e) = NonRec (substitute from to b) (substitute from to e)
  substitute from to (Rec ls) = Rec $ substitute from to ls

instance Substitutable Type (Id, CoreExpr) where
  substitute from _ _
    | not (isTyVar from) = panic "impossible substitution of term-level var -> type"
  substitute from to (lhs, rhs) = (substitute from to lhs, substitute from to rhs) 

{- Either term or type-level substitutiosn -}

instance Substitutable Var CoreExpr where
  -- | Essentially a renaming engine
  substitute from to (Var v) = Var $ substitute from to v
  substitute _ _ (Lit l) = Lit l
  substitute from to (App f x) = App (substitute from to f) (substitute from to x)
  substitute from to (Lam b e) = Lam (substitute from to b) (substitute from to e)
  substitute from to (Let b e) = Let (substitute from to b) (substitute from to e)
  substitute from to (Case e v t alts) = Case (substitute from to e)
                                              (substitute from to v)
                                              (substitute from to t)
                                              (substitute from to alts)
  substitute from to (Cast e c) = Cast (substitute from to e) c
  substitute from to (Tick c e) = Tick c (substitute from to e)
  substitute from to (Type t) = Type (substitute from to t)
  substitute _ _ (Coercion c) = Coercion c

instance Substitutable Var (Alt Var) where
  substitute from to (Alt alt_con vs e) = Alt alt_con
                                              (substitute from to vs)
                                              (substitute from to e)

instance Substitutable Var CoreBind where
  substitute from to (NonRec b e) = NonRec (substitute from to b) (substitute from to e)
  substitute from to (Rec ls) = Rec $ substitute from to ls

instance Substitutable Var (Id, CoreExpr) where
  substitute from to (lhs, rhs) = (substitute from to lhs, substitute from to rhs)

{- Term-level substitutions -}

{- The driver behind beta reduction -}
instance Substitutable CoreExpr CoreExpr where
  -- case of (\@a. ...) @b
  substitute from (Type t) e 
    | not (isTyVar from) = panic "impossible substitution of term-level var with type"
    | otherwise          = substitute from t e
  substitute from _ _
    | isTyVar from = panic "impossible substitution of type-level var with term"
  -- from and to are now term-level
  substitute from to e@(Var v)
    | from == v = to
    | otherwise = e
  substitute _ _ e@(Lit _) = e
  substitute from to (App f x) = App (substitute from to f)
                                     (substitute from to x)
  substitute from to (Lam b e) = Lam b (substitute from to e)
  substitute from to (Let b e) = Let (substitute from to b) (substitute from to e)
  substitute from to (Case e v t alts) = Case (substitute from to e)
                                              v
                                              t
                                              (substitute from to alts)
  substitute from to (Cast e c) = Cast (substitute from to e) c
  substitute from to (Tick c e) = Tick c (substitute from to e)
  substitute _ _ e@(Type _) = e
  substitute _ _ (Coercion c) = Coercion c

instance Substitutable CoreExpr CoreBind where
  substitute from (Type t) b 
    | not (isTyVar from) = panic "impossible substitution of term-level var with type"
    | otherwise          = substitute from t b
  substitute from _ _
    | isTyVar from = panic "impossible substitution of type-level var with term"
  substitute from to (NonRec lhs rhs) = NonRec lhs (substitute from to rhs)
  substitute from to (Rec ls) = Rec (substitute from to ls)

instance Substitutable CoreExpr (Id, CoreExpr) where
  substitute from (Type t) b 
    | not (isTyVar from) = panic "impossible substitution of term-level var with type"
    | otherwise          = substitute from t b
  substitute from _ _
    | isTyVar from = panic "impossible substitution of type-level var with term"
  substitute from to (lhs, rhs) = (lhs, substitute from to rhs) 

instance Substitutable CoreExpr (Alt Var) where
  substitute from (Type t) b 
    | not (isTyVar from) = panic "impossible substitution of term-level var with type"
    | otherwise          = substitute from t b
  substitute from _ _
    | isTyVar from = panic "impossible substitution of type-level var with term"
  substitute from to (Alt alt_con b e) = Alt alt_con b (substitute from to e)
  
