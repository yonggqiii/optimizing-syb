{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.DropCasts (dropCasts₁) where

import Control.Monad.Writer.Strict
import Data.Expr
import Data.List
import Data.Monoid (Sum (..), getSum)

dropCasts₁ :: Expr -> (Expr, Int)
dropCasts₁ x = let (a, b) = runWriter (dropCasts x) in (a, getSum b)

dropCasts :: Expr -> Writer (Sum Int) Expr
dropCasts (Cast e c) = do
  e' <- dropCasts e
  _ <- dropCastsCoercion c
  tell (Sum 1)
  return e'
dropCasts (Var i) = Var <$> dropCastsVar i
dropCasts (Lit l) = Lit <$> dropCastsLit l
dropCasts (App e e2) = App <$> dropCasts e <*> dropCasts e2
dropCasts (Lam b e) = Lam <$> dropCastsVar b <*> dropCasts e
dropCasts (Let b e) = Let <$> dropCastsBind b <*> dropCasts e
dropCasts (Case e v t alts) = Case <$> dropCasts e <*> dropCastsVar v <*> dropCastsType t <*> dropCastsListAlt alts
dropCasts (Type t) = Type <$> dropCastsType t
dropCasts (Coercion c) = Coercion <$> dropCastsCoercion c

dropCastsType :: Type -> Writer (Sum Int) Type
dropCastsType (TyVarTy v) = TyVarTy <$> dropCastsVar v
dropCastsType (AppTy a b) = AppTy <$> dropCastsType a <*> dropCastsType b
dropCastsType (MyTyConApp a b) = MyTyConApp <$> dropCastsMyTyCon a <*> dropCastsListType b
dropCastsType (ForAllTy a b) = ForAllTy <$> dropCastsVar a <*> dropCastsType b
dropCastsType (FunTy a b c) = FunTy <$> dropCastsType a <*> dropCastsType b <*> dropCastsType c
dropCastsType (LitTy l) = LitTy <$> dropCastsTyLit l
dropCastsType (CastTy t c) = do
  t' <- dropCastsType t
  _ <- dropCastsCoercion c
  tell (Sum 1)
  return t'
dropCastsType (CoercionTy c) = CoercionTy <$> dropCastsCoercion c

dropCastsTyLit :: TyLit -> Writer (Sum Int) TyLit
dropCastsTyLit (NumTyLit l) = NumTyLit <$> dropCastsInt l
dropCastsTyLit (StrTyLit s) = StrTyLit <$> dropCastsString s
dropCastsTyLit (CharTyLit c) = CharTyLit <$> dropCastsChar c

dropCastsListType :: List' Type -> Writer (Sum Int) (List' Type)
dropCastsListType Nil = return Nil
dropCastsListType (Cons x xs) = Cons <$> dropCastsType x <*> dropCastsListType xs

dropCastsListAlt :: List' Alt -> Writer (Sum Int) (List' Alt)
dropCastsListAlt Nil = return Nil
dropCastsListAlt (x `Cons` xs) = Cons <$> dropCastsAlt x <*> dropCastsListAlt xs

dropCastsAlt :: Alt -> Writer (Sum Int) Alt
dropCastsAlt (Alt ac lv e) = Alt <$> dropCastsAltCon ac <*> dropCastsListVar lv <*> dropCasts e

dropCastsListVar :: List' Var -> Writer (Sum Int) (List' Var)
dropCastsListVar Nil = return Nil
dropCastsListVar (Cons x xs) = Cons <$> dropCastsVar x <*> dropCastsListVar xs

dropCastsAltCon :: AltCon -> Writer (Sum Int) AltCon
dropCastsAltCon (DataAlt dc) = DataAlt <$> dropCastsDataCon dc
dropCastsAltCon (LitAlt l) = LitAlt <$> dropCastsLit l
dropCastsAltCon DEFAULT = return DEFAULT

dropCastsDataCon :: DataCon -> Writer (Sum Int) DataCon
dropCastsDataCon (MkData a b c d e f g) = MkData <$> dropCastsString a <*> dropCastsType b <*> dropCastsVar c <*> dropCastsMyTyCon d <*> dropCastsType e <*> dropCastsBool f <*> dropCastsMyTyCon g

dropCastsCoercion :: Coercion -> Writer (Sum Int) Coercion
dropCastsCoercion (MyRefl t) = MyRefl <$> dropCastsType t
dropCastsCoercion (GMyRefl a b c) = GMyRefl <$> dropCastsRole a <*> dropCastsType b <*> dropCastsCoercion c
dropCastsCoercion (MyTyConAppCo a b c) = MyTyConAppCo <$> dropCastsRole a <*> dropCastsMyTyCon b <*> dropCastsListCoercion c
dropCastsCoercion (AppCo a b) = AppCo <$> dropCastsCoercion a <*> dropCastsCoercion b
dropCastsCoercion (ForAllCo a b c) = ForAllCo <$> dropCastsVar a <*> dropCastsCoercion b <*> dropCastsCoercion c
dropCastsCoercion (FunCo a b c d) = FunCo <$> dropCastsRole a <*> dropCastsCoercion b <*> dropCastsCoercion c <*> dropCastsCoercion d
dropCastsCoercion (CoVarCo v) = CoVarCo <$> dropCastsVar v
dropCastsCoercion (SymCo s) = SymCo <$> dropCastsCoercion s
dropCastsCoercion (TransCo a b) = TransCo <$> dropCastsCoercion a <*> dropCastsCoercion b
dropCastsCoercion (InstCo a b) = InstCo <$> dropCastsCoercion a <*> dropCastsCoercion b
dropCastsCoercion (KindCo a) = KindCo <$> dropCastsCoercion a
dropCastsCoercion (SubCo a) = SubCo <$> dropCastsCoercion a

dropCastsListCoercion :: List' Coercion -> Writer (Sum Int) (List' Coercion)
dropCastsListCoercion Nil = return Nil
dropCastsListCoercion (Cons x xs) = Cons <$> dropCastsCoercion x <*> dropCastsListCoercion xs

dropCastsRole :: Role -> Writer (Sum Int) Role
dropCastsRole = return

dropCastsLit :: Literal -> Writer (Sum Int) Literal
dropCastsLit (LitChar c) = LitChar <$> dropCastsChar c
dropCastsLit (LitNumber i) = LitNumber <$> dropCastsInt i
dropCastsLit (LitString s) = LitString <$> dropCastsString s

dropCastsInt :: Integer -> Writer (Sum Int) Integer
dropCastsInt = return

dropCastsFunctionOrData :: FunctionOrData -> Writer (Sum Int) FunctionOrData
dropCastsFunctionOrData = return

dropCastsBind :: Bind -> Writer (Sum Int) Bind
dropCastsBind (NonRec b e) = NonRec <$> dropCastsVar b <*> dropCasts e
dropCastsBind (Rec ls) = Rec <$> dropCastsListPair ls

dropCastsListPair :: List' (Var, Expr) -> Writer (Sum Int) (List' (Var, Expr))
dropCastsListPair Nil = return Nil
dropCastsListPair (Cons x xs) = Cons <$> dropCastsPair x <*> dropCastsListPair xs

dropCastsPair :: (Var, Expr) -> Writer (Sum Int) (Var, Expr)
dropCastsPair (x, y) = (,) <$> dropCastsVar x <*> dropCasts y

dropCastsVar :: Var -> Writer (Sum Int) Var
dropCastsVar (TyVar a b) = TyVar <$> dropCastsString a <*> dropCastsType b
dropCastsVar (TcTyVar a b) = TcTyVar <$> dropCastsString a <*> dropCastsType b
dropCastsVar (Id n t m ids idd) = Id <$> dropCastsString n <*> dropCastsType t <*> dropCastsType m <*> dropCastsIdScope ids <*> dropCastsIdDetails idd

dropCastsIdScope :: IdScope -> Writer (Sum Int) IdScope
dropCastsIdScope GlobalId = return GlobalId
dropCastsIdScope (LocalId NotExported) = return (LocalId NotExported)
dropCastsIdScope (LocalId Exported) = return (LocalId Exported)

dropCastsIdDetails :: IdDetails -> Writer (Sum Int) IdDetails
dropCastsIdDetails VanillaId = return VanillaId
dropCastsIdDetails (DataConWorkId dc) = DataConWorkId <$> dropCastsDataCon dc
dropCastsIdDetails (DataConWrapId dc) = DataConWrapId <$> dropCastsDataCon dc
dropCastsIdDetails (ClassOpId c b) = ClassOpId <$> dropCastsClass c <*> dropCastsBool b
dropCastsIdDetails (DFunId b) = DFunId <$> dropCastsBool b
dropCastsIdDetails CoVarId = return CoVarId

dropCastsBool :: Bool -> Writer (Sum Int) Bool
dropCastsBool = return

dropCastsClass :: Class -> Writer (Sum Int) Class
dropCastsClass (Class a b c) = Class <$> dropCastsMyTyCon a <*> dropCastsString b <*> dropCastsListVar c

dropCastsMyTyCon :: MyTyCon -> Writer (Sum Int) MyTyCon
dropCastsMyTyCon (MyTyCon a b) = MyTyCon <$> dropCastsString a <*> dropCastsType b

dropCastsString :: String' -> Writer (Sum Int) String'
dropCastsString Nil = return Nil
dropCastsString (Cons x xs) = Cons <$> dropCastsChar x <*> dropCastsString xs

dropCastsChar :: Char -> Writer (Sum Int) Char
dropCastsChar = return

dropCastsTypeOrConstraint :: TypeOrConstraint -> Writer (Sum Int) TypeOrConstraint
dropCastsTypeOrConstraint = return
