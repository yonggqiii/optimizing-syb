{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.NumTypes (numTypes₁) where

import Data.Expr
import Data.List

go :: Int -> [Int] -> Int
go x [] = x
go x (y : ys) = go x ys + y

numTypes₁ :: Expr -> Int
numTypes₁ (Var x) = go 0 [sizeVar x]
numTypes₁ (App e1 e2) = go 0 [numTypes₁ e1, numTypes₁ e2]
numTypes₁ (Lit x) = go 0 [sizeLit x]
numTypes₁ (Lam v e) = go 0 [sizeVar v, numTypes₁ e]
numTypes₁ (Let b e) = go 0 [sizeBind b, numTypes₁ e]
numTypes₁ (Case e v t alts) = go 0 [numTypes₁ e, sizeVar v, sizeType t, sizeListAlt alts]
numTypes₁ (Cast e c) = go 0 [numTypes₁ e, sizeCoercion c]
numTypes₁ (Type t) = go 0 [sizeType t]
numTypes₁ (Coercion c) = go 0 [sizeCoercion c]

sizeLit :: Literal -> Int
sizeLit (LitChar x) = go 0 [sizeChar x]
sizeLit (LitString x) = go 0 [sizeString x]
sizeLit (LitNumber x) = go 0 [sizeNumber x]

sizeChar :: Char -> Int
sizeChar _ = go 0 [0]

sizeString :: String' -> Int
sizeString Nil = go 0 [0]
sizeString (Cons x xs) = go 0 [sizeChar x, sizeString xs]

sizeNumber :: Integer -> Int
sizeNumber _ = go 0 [0]

sizeVar :: Var -> Int
sizeVar (TyVar x y) = go 0 [sizeString x, sizeType y]
sizeVar (TcTyVar x y) = go 0 [sizeString x, sizeType y]
sizeVar (Id a t m b c) = go 0 [sizeType t, sizeType m, sizeIdScope b, sizeIdDetails c, sizeString a]

sizeIdScope :: IdScope -> Int
sizeIdScope GlobalId = go 0 [0]
sizeIdScope _ = go 0 [0]

sizeIdDetails :: IdDetails -> Int
sizeIdDetails VanillaId = go 0 [0]
sizeIdDetails (DataConWorkId x) = go 0 [sizeDataCon x]
sizeIdDetails (DataConWrapId x) = go 0 [sizeDataCon x]
sizeIdDetails (ClassOpId a _) = go 0 [sizeClass a]
sizeIdDetails (DFunId _) = go 0 [0]
sizeIdDetails CoVarId = go 0 [0]

sizeDataCon :: DataCon -> Int
sizeDataCon (MkData a b c d e _ g) = go 0 [sizeString a, sizeType b, sizeVar c, sizeMyTyCon d, sizeType e, sizeMyTyCon g]

sizeMyTyCon :: MyTyCon -> Int
sizeMyTyCon (MyTyCon a b) = go 0 [sizeString a, sizeType b]

sizeClass :: Class -> Int
sizeClass (Class a b c) = go 0 [sizeMyTyCon a, sizeString b, sizeListVar c]

sizeBind :: Bind -> Int
sizeBind (NonRec v e) = go 0 [sizeVar v, numTypes₁ e]
sizeBind (Rec ves) = go 0 [sizeListVarExpr ves]

sizeListVarExpr :: List' (Var, Expr) -> Int
sizeListVarExpr Nil = go 0 [0]
sizeListVarExpr (Cons (v, e) xs) = go 0 [sizeVar v, numTypes₁ e, sizeListVarExpr xs]

sizeListAlt :: List' Alt -> Int
sizeListAlt Nil = 0
sizeListAlt (Cons a as) = go 0 [sizeAlt a, sizeListAlt as]

sizeAlt :: Alt -> Int
sizeAlt (Alt con vs e) = go 0 [sizeAltCon con, sizeListVar vs, numTypes₁ e]

sizeAltCon :: AltCon -> Int
sizeAltCon (DataAlt c) = go 0 [sizeDataCon c]
sizeAltCon (LitAlt s) = go 0 [sizeLit s]
sizeAltCon DEFAULT = go 0 [0]

sizeListVar :: List' Var -> Int
sizeListVar Nil = go 0 [0]
sizeListVar (Cons v vs) = go 0 [sizeVar v, sizeListVar vs]

sizeType :: Type -> Int
sizeType (TyVarTy v) = go 1 [sizeVar v]
sizeType (AppTy t1 t2) = go 1 [sizeType t1, sizeType t2]
sizeType (MyTyConApp x ts) = go 1 [sizeListType ts, sizeMyTyCon x]
sizeType (ForAllTy v t) = go 1 [sizeVar v, sizeType t]
sizeType (FunTy m a r) = go 1 [sizeType m, sizeType a, sizeType r]
sizeType (LitTy x) = go 1 [sizeTyLit x]
sizeType (CastTy t c) = go 1 [sizeType t, sizeCoercion c]
sizeType (CoercionTy c) = go 1 [sizeCoercion c]

sizeTyLit :: TyLit -> Int
sizeTyLit (NumTyLit x) = go 0 [sizeNumber x]
sizeTyLit (StrTyLit x) = go 0 [sizeString x]
sizeTyLit (CharTyLit x) = go 0 [sizeChar x]

sizeListType :: List' Type -> Int
sizeListType Nil = go 0 [0]
sizeListType (Cons t ts) = go 0 [sizeType t, sizeListType ts]

sizeCoercion :: Coercion -> Int
sizeCoercion (MyRefl t) = go 0 [sizeType t]
sizeCoercion (GMyRefl x t c) = go 0 [sizeType t, sizeCoercion c, sizeRole x]
sizeCoercion (MyTyConAppCo a b cs) = go 0 [sizeListCoercion cs, sizeMyTyCon b, sizeRole a]
sizeCoercion (AppCo c1 c2) = go 0 [sizeCoercion c1, sizeCoercion c2]
sizeCoercion (ForAllCo v k c) = go 0 [sizeVar v, sizeCoercion k, sizeCoercion c]
sizeCoercion (FunCo x c1 c2 c3) = go 0 [sizeCoercion c1, sizeCoercion c2, sizeCoercion c3, sizeRole x]
sizeCoercion (CoVarCo v) = go 0 [sizeVar v]
sizeCoercion (SymCo c) = go 0 [sizeCoercion c]
sizeCoercion (TransCo c1 c2) = go 0 [sizeCoercion c1, sizeCoercion c2]
sizeCoercion (InstCo c1 c2) = go 0 [sizeCoercion c1, sizeCoercion c2]
sizeCoercion (KindCo c) = go 0 [sizeCoercion c]
sizeCoercion (SubCo c) = go 0 [sizeCoercion c]

sizeListCoercion :: List' Coercion -> Int
sizeListCoercion Nil = go 0 [0]
sizeListCoercion (Cons c cs) = go 0 [sizeCoercion c, sizeListCoercion cs]

sizeRole :: Role -> Int
sizeRole _ = go 0 [0]
