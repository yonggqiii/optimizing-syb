{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.IncInt (incInt₁) where

import Data.Expr
import Data.List

incInt₁ :: Expr -> Expr
incInt₁ (Var x) = Var $ incVar x
incInt₁ (Lit l) = Lit $ incLit l
incInt₁ (App a b) = App (incInt₁ a) (incInt₁ b)
incInt₁ (Lam b e) = Lam (incVar b) (incInt₁ e)
incInt₁ (Let b e) = Let (incBind b) (incInt₁ e)
incInt₁ (Case e v t alts) = Case (incInt₁ e) (incVar v) (incType t) (incAlts alts)
incInt₁ (Cast e c) = Cast (incInt₁ e) (incCoercion c)
incInt₁ (Type t) = Type (incType t)
incInt₁ (Coercion c) = Coercion (incCoercion c)

incCoercion :: Coercion -> Coercion
incCoercion (MyRefl t) = MyRefl (incType t)
incCoercion (GMyRefl a b c) = GMyRefl (incRole a) (incType b) (incCoercion c)
incCoercion (MyTyConAppCo a b c) =
  MyTyConAppCo
    (incRole a)
    (incMyTyCon b)
    (incCoercion <$> c)
incCoercion (AppCo a b) = AppCo (incCoercion a) (incCoercion b)
incCoercion (ForAllCo a b c) = ForAllCo (incVar a) (incCoercion b) (incCoercion c)
incCoercion (FunCo a b c d) = FunCo (incRole a) (incCoercion b) (incCoercion c) (incCoercion d)
incCoercion (CoVarCo x) = CoVarCo (incVar x)
incCoercion (SymCo x) = SymCo (incCoercion x)
incCoercion (TransCo a b) = TransCo (incCoercion a) (incCoercion b)
incCoercion (InstCo a b) = InstCo (incCoercion a) (incCoercion b)
incCoercion (KindCo a) = KindCo (incCoercion a)
incCoercion (SubCo a) = SubCo (incCoercion a)

incMyTyCon :: MyTyCon -> MyTyCon
incMyTyCon (MyTyCon n t) = MyTyCon (incString n) (incType t)

incString :: String' -> String'
incString Nil = Nil
incString (x `Cons` xs) = x `Cons` incString xs

incChar :: Char -> Char
incChar x = x

incRole :: Role -> Role
incRole Nominal = Nominal
incRole Representational = Representational
incRole Phantom = Phantom

incBind :: Bind -> Bind
incBind (NonRec b e) = NonRec (incVar b) (incInt₁ e)
incBind (Rec ls) = Rec $ (\(x, y) -> (incVar x, incInt₁ y)) <$> ls

incType :: Type -> Type
incType (TyVarTy v) = TyVarTy (incVar v)
incType (AppTy a b) = AppTy (incType a) (incType b)
incType (MyTyConApp e ls) = MyTyConApp (incMyTyCon e) (incType <$> ls)
incType (ForAllTy a t) = ForAllTy (incVar a) (incType t)
incType (FunTy a b c) = FunTy (incType a) (incType b) (incType c)
incType (LitTy x) = LitTy (incTyLit x)
incType (CastTy t c) = CastTy (incType t) (incCoercion c)
incType (CoercionTy c) = CoercionTy (incCoercion c)

incTyLit :: TyLit -> TyLit
incTyLit (NumTyLit x) = NumTyLit (x + 1)
incTyLit (StrTyLit s) = StrTyLit (incString s)
incTyLit (CharTyLit x) = CharTyLit (incChar x)

incAlts :: List' Alt -> List' Alt
incAlts Nil = Nil
incAlts (x `Cons` xs) = incAlt x `Cons` incAlts xs

incAlt :: Alt -> Alt
incAlt (Alt ac v e) = Alt (incAltCon ac) (incVar <$> v) (incInt₁ e)

incAltCon :: AltCon -> AltCon
incAltCon (DataAlt dc) = DataAlt (incDataCon dc)
incAltCon (LitAlt l) = LitAlt (incLit l)
incAltCon DEFAULT = DEFAULT

incDataCon :: DataCon -> DataCon
incDataCon (MkData a b c d e f g) = MkData (incString a) (incType b) (incVar c) (incMyTyCon d) (incType e) (incBool f) (incMyTyCon g)

incBool :: Bool -> Bool
incBool True = True
incBool False = False

incVar :: Var -> Var
incVar (TyVar a b) = TyVar (incString a) (incType b)
incVar (TcTyVar a b) = TcTyVar (incString a) (incType b)
incVar (Id a b c d e) = Id (incString a) (incType b) (incType c) (incIdScope d) (incIdDetails e)

incIdScope :: IdScope -> IdScope
incIdScope GlobalId = GlobalId
incIdScope (LocalId NotExported) = LocalId NotExported
incIdScope (LocalId Exported) = LocalId Exported

incIdDetails :: IdDetails -> IdDetails
incIdDetails VanillaId = VanillaId
incIdDetails (DataConWorkId x) = DataConWorkId (incDataCon x)
incIdDetails (DataConWrapId x) = DataConWrapId (incDataCon x)
incIdDetails (ClassOpId a b) = ClassOpId (incClass a) (incBool b)
incIdDetails (DFunId a) = DFunId (incBool a)
incIdDetails CoVarId = CoVarId

incClass :: Class -> Class
incClass (Class a b c) = Class (incMyTyCon a) (incString b) (incVar <$> c)

incLit :: Literal -> Literal
incLit (LitNumber x) = LitNumber (x + 1)
incLit x = x
