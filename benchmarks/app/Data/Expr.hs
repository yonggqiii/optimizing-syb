{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module Data.Expr where

import Control.DeepSeq
import Data.Data
import Data.Data3
import Data.List

-------------------------------------------------------------------------------
--
-- Definition of the Expr type
--
--   This is an excerpt of the 'GHC.Core.Expr' type, to demonstrate the
--   efficiency of traversals over large recursive data structures.
--
-------------------------------------------------------------------------------
data Expr
  = Var Id
  | Lit Literal
  | App Expr Arg
  | Lam Var Expr
  | Let Bind Expr
  | Case Expr Var Type (List' Alt)
  | Cast Expr Coercion
  | Type Type
  | Coercion Coercion
  deriving (Show, Eq, Data)

data Bind
  = NonRec Var Expr
  | Rec (List' (Var, Expr))
  deriving (Show, Eq, Data)

type Arg = Expr

data Alt
  = Alt AltCon (List' Var) Expr
  deriving (Data, Show, Eq)

data AltCon
  = DataAlt DataCon
  | LitAlt Literal
  | DEFAULT
  deriving (Eq, Data, Show)

type Name = String'

data Var
  = TyVar
      { varName :: !Name,
        varType :: Kind
      }
  | TcTyVar
      { varName :: !Name,
        varType :: Kind
      }
  | Id
      { varName :: !Name,
        varType :: Type,
        varMult :: Mult,
        idScope :: IdScope,
        id_details :: IdDetails
      }
  deriving (Show, Eq, Data)

type Mult = Type

data IdDetails
  = VanillaId
  | DataConWorkId DataCon
  | DataConWrapId DataCon
  | ClassOpId
      Class
      Bool
  | DFunId Bool
  | CoVarId
  deriving (Show, Eq, Data)

data Class
  = Class
  { classMyTyCon :: MyTyCon,
    className :: Name,
    classTyVars :: List' TyVar
  }
  deriving (Show, Eq, Data)

type TyVar = Var

data TypeOrConstraint = TypeLike | ConstraintLike deriving (Show, Data, Eq)

data IdScope
  = GlobalId
  | LocalId ExportFlag
  deriving (Show, Eq, Data)

data ExportFlag
  = NotExported
  | Exported
  deriving (Show, Eq, Data)

type Id = Var

data Literal
  = LitChar Char
  | LitNumber !Integer
  | LitString !String'
  deriving (Data, Show, Eq)

data FunctionOrData = IsFunction | IsData
  deriving (Eq, Ord, Data, Show)

type KindOrType = Type

type Kind = Type

type RuntimeRepType = Type

type LevityType = Type

type FRRType = Type

type ForAllTyBinder = Var

data Type
  = TyVarTy Var
  | AppTy
      Type
      Type
  | MyTyConApp
      MyTyCon
      (List' KindOrType)
  | ForAllTy
      !ForAllTyBinder
      Type
  | FunTy
      { ft_mult :: Mult,
        ft_arg :: Type,
        ft_res :: Type
      }
  | LitTy TyLit
  | CastTy
      Type
      KindCoercion
  | CoercionTy
      Coercion
  deriving (Data, Show, Eq)

type KindCoercion = Coercion

data TyLit
  = NumTyLit Integer
  | StrTyLit String'
  | CharTyLit Char
  deriving (Eq, Data, Show)

type TyCoVar = Var

type CoVar = Var

data Coercion
  = MyRefl Type
  | GMyRefl Role Type Coercion
  | MyTyConAppCo Role MyTyCon (List' Coercion)
  | AppCo Coercion Coercion
  | ForAllCo TyCoVar KindCoercion Coercion
  | FunCo
      { fco_role :: Role,
        fco_mult :: Coercion,
        fco_arg, fco_res :: Coercion
      }
  | CoVarCo CoVar
  | SymCo Coercion
  | TransCo Coercion Coercion
  | InstCo Coercion Coercion
  | KindCo Coercion
  | SubCo Coercion
  deriving (Data, Eq, Show)

data Role = Nominal | Representational | Phantom deriving (Data, Eq, Ord, Show)

data DataCon
  = MkData
  { dcName :: Name,
    dcOrigResTy :: Type,
    dcWorkId :: Id,
    dcRepMyTyCon :: MyTyCon,
    dcRepType :: Type,
    dcInfix :: Bool,
    dcPromoted :: MyTyCon
  }
  deriving (Show, Eq, Data)

data MyTyCon = MyTyCon
  { tyConName :: !Name,
    tyConResKind :: Kind
  }
  deriving (Show, Eq, Data)

-------------------------------------------------------------------------------
--
-- Convenience functions for creating expressions
--
-------------------------------------------------------------------------------

mkExpr :: Int -> Expr
mkExpr 0 = Lit (mkLit 0)
mkExpr 1 = Lit (mkLit 0)
mkExpr 2 = Lit (mkLit 1)
mkExpr 3 = Var (mkVar 2)
mkExpr n
  | m == 0 = App (mkExpr (n - 1)) (mkExpr (n - 1))
  | m == 1 = Lam (mkVar (n - 1)) (mkExpr (n - 1))
  | m == 2 = Let (mkBind (n - 1)) (mkExpr (n - 1))
  | m == 3 =
      Case
        (mkExpr (n - 1))
        (mkVar (n - 1))
        (mkType (n - 1))
        (mkListAlts (n - 1))
  | otherwise = Cast (mkExpr (n - 1)) (mkCoercion (n - 1))
  where
    m = n `mod` 5

mkVar :: Int -> Var
mkVar n
  | m == 0 = TyVar (fromNativeList "someTyVar") (mkType 0)
  | m == 1 = TcTyVar (fromNativeList "someTcTyVar") (mkType 0)
  | otherwise =
      Id
        (fromNativeList "someId")
        (mkType (n - 1))
        (mkType (n - 1))
        (mkIdScope (n - 1))
        (mkIdDetails (n - 1))
  where
    m = n `mod` 3

mkLit :: Int -> Literal
mkLit n
  | m == 0 = LitChar 'x'
  | m == 1 = LitNumber 1234
  | otherwise = LitString $ fromNativeList "someLiteralString"
  where
    m = n `mod` 3

mkIdScope :: Int -> IdScope
mkIdScope n
  | n `mod` 3 == 0 = GlobalId
  | n `mod` 3 == 1 = LocalId Exported
  | otherwise = LocalId NotExported

mkIdDetails :: Int -> IdDetails
mkIdDetails 0 = VanillaId
mkIdDetails 1 = CoVarId
mkIdDetails 2 = DFunId True
mkIdDetails n
  | n `mod` 3 == 0 = DataConWorkId (mkDataCon (n - 1))
  | n `mod` 3 == 1 = DataConWrapId (mkDataCon (n - 1))
  | otherwise = ClassOpId (mkClass (n - 1)) (odd n)

mkBind :: Int -> Bind
mkBind 0 = NonRec (mkVar 0) (mkExpr 0)
mkBind n
  | even n = NonRec (mkVar (n - 1)) (mkExpr (n - 1))
  | otherwise = Rec (mkListPairVarExpr (n - 1))

mkListPairVarExpr :: Int -> List' (Var, Expr)
mkListPairVarExpr 0 = Nil
mkListPairVarExpr n =
  Cons
    (mkVar (n - 1), mkExpr (n - 1))
    (mkListPairVarExpr (n - 1))

mkType :: Int -> Type
mkType 0 = LitTy (NumTyLit 123)
mkType 1 = LitTy (StrTyLit (fromNativeList "someLitTy"))
mkType 2 = LitTy (CharTyLit 'x')
mkType n
  | m == 0 = TyVarTy (mkVar (n - 1))
  | m == 1 = AppTy (mkType (n - 1)) (mkType (n - 2))
  | m == 2 = MyTyConApp (mkMyTyCon (n - 1)) (mkListType (n - 1))
  | m == 3 = ForAllTy (mkVar (n - 1)) (mkType (n - 2))
  | m == 4 = FunTy (mkType (n - 1)) (mkType (n - 2)) (mkType (n - 3))
  | m == 5 = CastTy (mkType (n - 1)) (mkCoercion (n - 2))
  | otherwise = CoercionTy (mkCoercion (n - 1))
  where
    m = n `mod` 7

mkListAlts :: Int -> List' Alt
mkListAlts 0 = Nil
mkListAlts n = Cons (mkAlt n) (mkListAlts (n - 1))

mkAlt :: Int -> Alt
mkAlt 0 = Alt DEFAULT Nil (mkExpr 0)
mkAlt n = Alt (mkAltCon (n - 1)) (mkListVars (n - 1)) (mkExpr (n - 1))

mkAltCon :: Int -> AltCon
mkAltCon 0 = DEFAULT
mkAltCon n
  | even n = LitAlt (mkLit (n - 1))
  | otherwise = DataAlt (mkDataCon (n - 1))

mkCoercion :: Int -> Coercion
mkCoercion 0 = MyRefl (mkType 0)
mkCoercion n
  | m == 0 = MyRefl (mkType (n - 1))
  | m == 1 = GMyRefl (mkRole (n - 1)) (mkType (n - 1)) (mkCoercion (n - 1))
  | m == 2 =
      MyTyConAppCo
        (mkRole (n - 1))
        (mkMyTyCon (n - 2))
        (mkListCoercion (n - 2))
  | m == 3 = AppCo (mkCoercion (n - 1)) (mkCoercion (n - 2))
  | m == 4 = ForAllCo (mkVar (n - 1)) (mkCoercion (n - 2)) (mkCoercion (n - 3))
  | m == 5 =
      FunCo
        (mkRole (n - 1))
        (mkCoercion (n - 2))
        (mkCoercion (n - 3))
        (mkCoercion (n - 4))
  | m == 6 = CoVarCo (mkVar (n - 1))
  | m == 7 = SymCo (mkCoercion (n - 2))
  | m == 8 = TransCo (mkCoercion (n - 1)) (mkCoercion (n - 3))
  | m == 9 = InstCo (mkCoercion (n - 1)) (mkCoercion (n - 4))
  | m == 10 = KindCo (mkCoercion (n - 1))
  | otherwise = SubCo (mkCoercion (n - 1))
  where
    m = n `mod` 12

mkRole :: Int -> Role
mkRole n
  | n `mod` 3 == 0 = Nominal
  | n `mod` 3 == 1 = Representational
  | otherwise = Phantom

mkListCoercion :: Int -> List' Coercion
mkListCoercion 0 = Nil
mkListCoercion n = mkCoercion (n - 1) `Cons` mkListCoercion (n - 1)

mkListType :: Int -> List' Type
mkListType 0 = Nil
mkListType n = mkType (n - 1) `Cons` mkListType (n - 1)

mkMyTyCon :: Int -> MyTyCon
mkMyTyCon 0 = MyTyCon (fromNativeList "someMyTyCon") (mkType 0)
mkMyTyCon n = MyTyCon (fromNativeList "someMyTyCon") (mkType (n - 1))

mkListVars :: Int -> List' Var
mkListVars 0 = Nil
mkListVars n = mkVar (n - 1) `Cons` mkListVars (n - 1)

mkDataCon :: Int -> DataCon
mkDataCon 0 =
  MkData
    (fromNativeList "someDataCon")
    (mkType 0)
    (mkVar 0)
    (mkMyTyCon 0)
    (mkType 0)
    False
    (mkMyTyCon 0)
mkDataCon n =
  MkData
    (fromNativeList "someDataCon")
    (mkType (n - 1))
    (mkVar (n - 1))
    (mkMyTyCon (n - 1))
    (mkType (n - 1))
    (even n)
    (mkMyTyCon (n - 1))

mkClass :: Int -> Class
mkClass 0 =
  Class
    (mkMyTyCon 0)
    (fromNativeList "someClass")
    (mkListVar 0)
mkClass n =
  Class
    (mkMyTyCon (n - 1))
    (fromNativeList "someClass")
    (mkListVar (n - 1))

mkListVar :: Int -> List' Var
mkListVar 0 = Nil
mkListVar n = mkVar (n - 1) `Cons` mkListVar (n - 1)

instance (γ Role) => Data₃ γ Role where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ FunctionOrData) => Data₃ γ FunctionOrData where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ TypeOrConstraint) => Data₃ γ TypeOrConstraint where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ Integer, γ Char, γ String', γ TyLit) => Data₃ γ TyLit where
  gmapT₃ _ f (NumTyLit x) = NumTyLit (f x)
  gmapT₃ _ f (StrTyLit x) = StrTyLit (f x)
  gmapT₃ _ f (CharTyLit x) = CharTyLit (f x)
  gmapQ₃ _ f (NumTyLit x) = [f x]
  gmapQ₃ _ f (StrTyLit x) = [f x]
  gmapQ₃ _ f (CharTyLit x) = [f x]
  gmapM₃ _ f (NumTyLit x) = NumTyLit <$> f x
  gmapM₃ _ f (StrTyLit x) = StrTyLit <$> f x
  gmapM₃ _ f (CharTyLit x) = CharTyLit <$> f x

instance (γ Integer, γ Char, γ String', γ Literal) => Data₃ γ Literal where
  gmapT₃ _ f (LitNumber x) = LitNumber (f x)
  gmapT₃ _ f (LitString x) = LitString (f x)
  gmapT₃ _ f (LitChar x) = LitChar (f x)
  gmapQ₃ _ f (LitNumber x) = [f x]
  gmapQ₃ _ f (LitString x) = [f x]
  gmapQ₃ _ f (LitChar x) = [f x]
  gmapM₃ _ f (LitNumber x) = LitNumber <$> f x
  gmapM₃ _ f (LitString x) = LitString <$> f x
  gmapM₃ _ f (LitChar x) = LitChar <$> f x

instance (γ ExportFlag) => Data₃ γ ExportFlag where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ ExportFlag, γ IdScope) => Data₃ γ IdScope where
  gmapT₃ _ _ GlobalId = GlobalId
  gmapT₃ _ f (LocalId x) = LocalId (f x)
  gmapQ₃ _ _ GlobalId = []
  gmapQ₃ _ f (LocalId x) = [f x]
  gmapM₃ _ _ GlobalId = return GlobalId
  gmapM₃ _ f (LocalId x) = LocalId <$> f x

instance
  ( γ Expr,
    γ Var,
    γ Integer,
    γ Char,
    γ String',
    γ Literal,
    γ Type,
    γ Coercion,
    γ Bind,
    γ Alt,
    γ (List' Alt),
    γ (Var, Expr),
    γ (List' (Var, Expr)),
    γ AltCon,
    γ (List' Var),
    γ IdDetails,
    γ DataCon,
    γ ExportFlag,
    γ IdScope,
    γ Bool,
    γ Class,
    γ MyTyCon,
    γ TyLit,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ Expr
  where
  gmapT₃ _ f (Var x) = Var $ f x
  gmapT₃ _ f (Lit l) = Lit $ f l
  gmapT₃ _ f (App e e') = App (f e) (f e')
  gmapT₃ _ f (Lam e e') = Lam (f e) (f e')
  gmapT₃ _ f (Let e e') = Let (f e) (f e')
  gmapT₃ _ f (Case a b c d) = Case (f a) (f b) (f c) (f d)
  gmapT₃ _ f (Cast e e') = Cast (f e) (f e')
  gmapT₃ _ f (Type l) = Type $ f l
  gmapT₃ _ f (Coercion l) = Coercion $ f l
  gmapQ₃ _ f (Var x) = [f x]
  gmapQ₃ _ f (Lit x) = [f x]
  gmapQ₃ _ f (Type x) = [f x]
  gmapQ₃ _ f (Coercion x) = [f x]
  gmapQ₃ _ f (App x y) = [f x, f y]
  gmapQ₃ _ f (Let x y) = [f x, f y]
  gmapQ₃ _ f (Cast x y) = [f x, f y]
  gmapQ₃ _ f (Lam x y) = [f x, f y]
  gmapQ₃ _ f (Case a b c d) = [f a, f b, f c, f d]
  gmapM₃ _ f (Var x) = Var <$> f x
  gmapM₃ _ f (Lit x) = Lit <$> f x
  gmapM₃ _ f (Type x) = Type <$> f x
  gmapM₃ _ f (Coercion x) = Coercion <$> f x
  gmapM₃ _ f (App x y) = App <$> f x <*> f y
  gmapM₃ _ f (Let x y) = Let <$> f x <*> f y
  gmapM₃ _ f (Cast x y) = Cast <$> f x <*> f y
  gmapM₃ _ f (Lam x y) = Lam <$> f x <*> f y
  gmapM₃ _ f (Case a b c d) = Case <$> f a <*> f b <*> f c <*> f d

instance
  ( γ Bind,
    γ Var,
    γ Expr,
    γ Integer,
    γ Char,
    γ String',
    γ Literal,
    γ Type,
    γ Coercion,
    γ Alt,
    γ (List' Alt),
    γ (Var, Expr),
    γ (List' (Var, Expr)),
    γ AltCon,
    γ (List' Var),
    γ DataCon,
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ Bool,
    γ Class,
    γ MyTyCon,
    γ TyLit,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ Bind
  where
  gmapT₃ _ f (NonRec x y) = NonRec (f x) (f y)
  gmapT₃ _ f (Rec ls) = Rec (f ls)
  gmapQ₃ _ f (NonRec x y) = [f x, f y]
  gmapQ₃ _ f (Rec ls) = [f ls]
  gmapM₃ _ f (NonRec x y) = NonRec <$> f x <*> f y
  gmapM₃ _ f (Rec ls) = Rec <$> f ls

instance
  ( γ Alt,
    γ AltCon,
    γ Var,
    γ (List' Var),
    γ Expr,
    γ Integer,
    γ Char,
    γ String',
    γ Literal,
    γ Type,
    γ Coercion,
    γ Bind,
    γ (List' Alt),
    γ (Var, Expr),
    γ (List' (Var, Expr)),
    γ DataCon,
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ Bool,
    γ Class,
    γ MyTyCon,
    γ TyLit,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ Alt
  where
  gmapT₃ _ f (Alt a b c) = Alt (f a) (f b) (f c)
  gmapQ₃ _ f (Alt a b c) = [f a, f b, f c]
  gmapM₃ _ f (Alt a b c) = Alt <$> f a <*> f b <*> f c

instance
  ( γ AltCon,
    γ DataCon,
    γ Integer,
    γ Char,
    γ String',
    γ Literal,
    γ Type,
    γ Var,
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ Bool,
    γ Class,
    γ (List' Var),
    γ MyTyCon,
    γ TyLit,
    γ Coercion,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ AltCon
  where
  gmapT₃ _ _ DEFAULT = DEFAULT
  gmapT₃ _ f (DataAlt x) = DataAlt (f x)
  gmapT₃ _ f (LitAlt x) = LitAlt (f x)
  gmapQ₃ _ _ DEFAULT = []
  gmapQ₃ _ f (DataAlt x) = [f x]
  gmapQ₃ _ f (LitAlt x) = [f x]
  gmapM₃ _ _ DEFAULT = return DEFAULT
  gmapM₃ _ f (DataAlt x) = DataAlt <$> f x
  gmapM₃ _ f (LitAlt x) = LitAlt <$> f x

instance
  ( γ Var,
    γ Type,
    γ Char,
    γ String',
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ DataCon,
    γ Bool,
    γ Class,
    γ (List' Var),
    γ MyTyCon,
    γ Integer,
    γ TyLit,
    γ Coercion,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ Var
  where
  gmapT₃ _ f (TyVar a b) = TyVar (f a) (f b)
  gmapT₃ _ f (TcTyVar a b) = TcTyVar (f a) (f b)
  gmapT₃ _ f (Id a b c d e) = Id (f a) (f b) (f c) (f d) (f e)
  gmapQ₃ _ f (TyVar a b) = [f a, f b]
  gmapQ₃ _ f (TcTyVar a b) = [f a, f b]
  gmapQ₃ _ f (Id a b c d e) = [f a, f b, f c, f d, f e]
  gmapM₃ _ f (TyVar a b) = TyVar <$> f a <*> f b
  gmapM₃ _ f (TcTyVar a b) = TcTyVar <$> f a <*> f b
  gmapM₃ _ f (Id a b c d e) = Id <$> f a <*> f b <*> f c <*> f d <*> f e

instance
  ( γ IdDetails,
    γ DataCon,
    γ Bool,
    γ Class,
    γ (List' Var),
    γ Var,
    γ Type,
    γ ExportFlag,
    γ IdScope,
    γ Char,
    γ String',
    γ MyTyCon,
    γ Integer,
    γ TyLit,
    γ Coercion,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ IdDetails
  where
  gmapT₃ _ _ VanillaId = VanillaId
  gmapT₃ _ _ CoVarId = CoVarId
  gmapT₃ _ f (DataConWorkId x) = DataConWorkId (f x)
  gmapT₃ _ f (DataConWrapId x) = DataConWrapId (f x)
  gmapT₃ _ f (DFunId x) = DFunId (f x)
  gmapT₃ _ f (ClassOpId x y) = ClassOpId (f x) (f y)
  gmapQ₃ _ _ VanillaId = []
  gmapQ₃ _ _ CoVarId = []
  gmapQ₃ _ f (DataConWorkId x) = [f x]
  gmapQ₃ _ f (DataConWrapId x) = [f x]
  gmapQ₃ _ f (DFunId x) = [f x]
  gmapQ₃ _ f (ClassOpId x y) = [f x, f y]
  gmapM₃ _ _ VanillaId = return VanillaId
  gmapM₃ _ _ CoVarId = return CoVarId
  gmapM₃ _ f (DataConWorkId x) = DataConWorkId <$> f x
  gmapM₃ _ f (DataConWrapId x) = DataConWrapId <$> f x
  gmapM₃ _ f (DFunId x) = DFunId <$> f x
  gmapM₃ _ f (ClassOpId x y) = ClassOpId <$> f x <*> f y

instance
  ( γ Class,
    γ (List' Var),
    γ Var,
    γ Type,
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ DataCon,
    γ Bool,
    γ Char,
    γ String',
    γ MyTyCon,
    γ Integer,
    γ TyLit,
    γ Coercion,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ Class
  where
  gmapT₃ _ f (Class x y z) = Class (f x) (f y) (f z)
  gmapQ₃ _ f (Class x y z) = [f x, f y, f z]
  gmapM₃ _ f (Class x y z) = Class <$> f x <*> f y <*> f z

instance
  ( γ Type,
    γ Var,
    γ Char,
    γ String',
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ DataCon,
    γ Bool,
    γ Class,
    γ (List' Var),
    γ MyTyCon,
    γ Integer,
    γ TyLit,
    γ Coercion,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ Type
  where
  gmapT₃ _ f (TyVarTy a) = TyVarTy (f a)
  gmapT₃ _ f (LitTy a) = LitTy (f a)
  gmapT₃ _ f (CoercionTy a) = CoercionTy (f a)
  gmapT₃ _ f (AppTy a b) = AppTy (f a) (f b)
  gmapT₃ _ f (MyTyConApp a b) = MyTyConApp (f a) (f b)
  gmapT₃ _ f (ForAllTy a b) = ForAllTy (f a) (f b)
  gmapT₃ _ f (CastTy a b) = CastTy (f a) (f b)
  gmapT₃ _ f (FunTy a b c) = FunTy (f a) (f b) (f c)
  gmapQ₃ _ f (TyVarTy a) = [f a]
  gmapQ₃ _ f (LitTy a) = [f a]
  gmapQ₃ _ f (CoercionTy a) = [f a]
  gmapQ₃ _ f (AppTy a b) = [f a, f b]
  gmapQ₃ _ f (MyTyConApp a b) = [f a, f b]
  gmapQ₃ _ f (ForAllTy a b) = [f a, f b]
  gmapQ₃ _ f (CastTy a b) = [f a, f b]
  gmapQ₃ _ f (FunTy a b c) = [f a, f b, f c]
  gmapM₃ _ f (TyVarTy a) = TyVarTy <$> f a
  gmapM₃ _ f (LitTy a) = LitTy <$> f a
  gmapM₃ _ f (CoercionTy a) = CoercionTy <$> f a
  gmapM₃ _ f (AppTy a b) = AppTy <$> f a <*> f b
  gmapM₃ _ f (MyTyConApp a b) = MyTyConApp <$> f a <*> f b
  gmapM₃ _ f (ForAllTy a b) = ForAllTy <$> f a <*> f b
  gmapM₃ _ f (CastTy a b) = CastTy <$> f a <*> f b
  gmapM₃ _ f (FunTy a b c) = FunTy <$> f a <*> f b <*> f c

instance
  ( γ Coercion,
    γ Type,
    γ Var,
    γ Char,
    γ String',
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ DataCon,
    γ Bool,
    γ Class,
    γ (List' Var),
    γ MyTyCon,
    γ Integer,
    γ TyLit,
    γ (List' Type),
    γ Role,
    γ (List' Coercion)
  ) =>
  Data₃ γ Coercion
  where
  gmapT₃ _ f (MyRefl a) = MyRefl (f a)
  gmapT₃ _ f (CoVarCo a) = CoVarCo (f a)
  gmapT₃ _ f (SymCo a) = SymCo (f a)
  gmapT₃ _ f (KindCo a) = KindCo (f a)
  gmapT₃ _ f (SubCo a) = SubCo (f a)
  gmapT₃ _ f (AppCo a b) = AppCo (f a) (f b)
  gmapT₃ _ f (TransCo a b) = TransCo (f a) (f b)
  gmapT₃ _ f (InstCo a b) = InstCo (f a) (f b)
  gmapT₃ _ f (GMyRefl a b c) = GMyRefl (f a) (f b) (f c)
  gmapT₃ _ f (MyTyConAppCo a b c) = MyTyConAppCo (f a) (f b) (f c)
  gmapT₃ _ f (ForAllCo a b c) = ForAllCo (f a) (f b) (f c)
  gmapT₃ _ f (FunCo a b c d) = FunCo (f a) (f b) (f c) (f d)
  gmapQ₃ _ f (MyRefl a) = [f a]
  gmapQ₃ _ f (CoVarCo a) = [f a]
  gmapQ₃ _ f (SymCo a) = [f a]
  gmapQ₃ _ f (KindCo a) = [f a]
  gmapQ₃ _ f (SubCo a) = [f a]
  gmapQ₃ _ f (AppCo a b) = [f a, f b]
  gmapQ₃ _ f (TransCo a b) = [f a, f b]
  gmapQ₃ _ f (InstCo a b) = [f a, f b]
  gmapQ₃ _ f (GMyRefl a b c) = [f a, f b, f c]
  gmapQ₃ _ f (MyTyConAppCo a b c) = [f a, f b, f c]
  gmapQ₃ _ f (ForAllCo a b c) = [f a, f b, f c]
  gmapQ₃ _ f (FunCo a b c d) = [f a, f b, f c, f d]
  gmapM₃ _ f (MyRefl a) = MyRefl <$> f a
  gmapM₃ _ f (CoVarCo a) = CoVarCo <$> f a
  gmapM₃ _ f (SymCo a) = SymCo <$> f a
  gmapM₃ _ f (KindCo a) = KindCo <$> f a
  gmapM₃ _ f (SubCo a) = SubCo <$> f a
  gmapM₃ _ f (AppCo a b) = AppCo <$> f a <*> f b
  gmapM₃ _ f (TransCo a b) = TransCo <$> f a <*> f b
  gmapM₃ _ f (InstCo a b) = InstCo <$> f a <*> f b
  gmapM₃ _ f (GMyRefl a b c) = GMyRefl <$> f a <*> f b <*> f c
  gmapM₃ _ f (MyTyConAppCo a b c) = MyTyConAppCo <$> f a <*> f b <*> f c
  gmapM₃ _ f (ForAllCo a b c) = ForAllCo <$> f a <*> f b <*> f c
  gmapM₃ _ f (FunCo a b c d) = FunCo <$> f a <*> f b <*> f c <*> f d

instance
  ( γ DataCon,
    γ Type,
    γ Var,
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ Bool,
    γ Class,
    γ (List' Var),
    γ MyTyCon,
    γ Integer,
    γ TyLit,
    γ Coercion,
    γ (List' Type),
    γ Role,
    γ (List' Coercion),
    γ Char,
    γ String'
  ) =>
  Data₃ γ DataCon
  where
  gmapT₃ _ f (MkData a b c d e g h) =
    MkData
      (f a)
      (f b)
      (f c)
      (f d)
      (f e)
      (f g)
      (f h)
  gmapQ₃ _ f (MkData a b c d e g h) = [f a, f b, f c, f d, f e, f g, f h]
  gmapM₃ _ f (MkData a b c d e g h) =
    MkData
      <$> f a
      <*> f b
      <*> f c
      <*> f d
      <*> f e
      <*> f g
      <*> f h

instance
  ( γ MyTyCon,
    γ Type,
    γ Var,
    γ IdDetails,
    γ ExportFlag,
    γ IdScope,
    γ DataCon,
    γ Bool,
    γ Class,
    γ (List' Var),
    γ Integer,
    γ TyLit,
    γ Coercion,
    γ (List' Type),
    γ Role,
    γ (List' Coercion),
    γ Char,
    γ String'
  ) =>
  Data₃ γ MyTyCon
  where
  gmapT₃ _ f (MyTyCon a b) = MyTyCon (f a) (f b)
  gmapQ₃ _ f (MyTyCon a b) = [f a, f b]
  gmapM₃ _ f (MyTyCon a b) = MyTyCon <$> f a <*> f b

-------------------------------------------------------------------------------
--
-- NFData instances for benchmarking
--
-------------------------------------------------------------------------------

instance NFData Expr where
  rnf (Var x) = rnf x
  rnf (Lit x) = rnf x
  rnf (App e x) = rnf (e, x)
  rnf (Lam e x) = rnf (e, x)
  rnf (Let e x) = rnf (e, x)
  rnf (Cast e x) = rnf (e, x)
  rnf (Type e) = rnf e
  rnf (Coercion e) = rnf e
  rnf (Case a b c d) = rnf (a, b, c, d)

instance NFData Bind where
  rnf (NonRec a b) = rnf (a, b)
  rnf (Rec ls) = rnf ls

instance NFData Alt where
  rnf (Alt a b c) = rnf (a, b, c)

instance NFData AltCon where
  rnf (DataAlt x) = rnf x
  rnf (LitAlt x) = rnf x
  rnf DEFAULT = ()

instance NFData Var where
  rnf (TyVar x y) = rnf (x, y)
  rnf (TcTyVar x y) = rnf (x, y)
  rnf (Id a b c d e) = rnf (a, b, c, d, e)

instance NFData IdDetails where
  rnf VanillaId = ()
  rnf (DataConWorkId x) = rnf x
  rnf (DataConWrapId x) = rnf x
  rnf CoVarId = ()
  rnf (DFunId x) = rnf x
  rnf (ClassOpId x y) = rnf (x, y)

instance NFData Class where
  rnf (Class a b c) = rnf (a, b, c)

instance NFData TypeOrConstraint where
  rnf TypeLike = ()
  rnf ConstraintLike = ()

instance NFData IdScope where
  rnf GlobalId = ()
  rnf (LocalId x) = rnf x

instance NFData ExportFlag where
  rnf NotExported = ()
  rnf Exported = ()

instance NFData Literal where
  rnf (LitChar x) = rnf x
  rnf (LitNumber x) = rnf x
  rnf (LitString x) = rnf x

instance NFData FunctionOrData where
  rnf IsFunction = ()
  rnf IsData = ()

instance NFData Type where
  rnf (TyVarTy x) = rnf x
  rnf (AppTy a b) = rnf (a, b)
  rnf (MyTyConApp a b) = rnf (a, b)
  rnf (ForAllTy a b) = rnf (a, b)
  rnf (FunTy a b c) = rnf (a, b, c)
  rnf (LitTy x) = rnf x
  rnf (CastTy x y) = rnf (x, y)
  rnf (CoercionTy x) = rnf x

instance NFData TyLit where
  rnf (NumTyLit x) = rnf x
  rnf (StrTyLit x) = rnf x
  rnf (CharTyLit x) = rnf x

instance NFData Coercion where
  rnf (MyRefl x) = rnf x
  rnf (CoVarCo x) = rnf x
  rnf (SymCo x) = rnf x
  rnf (KindCo x) = rnf x
  rnf (SubCo x) = rnf x
  rnf (AppCo a b) = rnf (a, b)
  rnf (TransCo a b) = rnf (a, b)
  rnf (InstCo a b) = rnf (a, b)
  rnf (GMyRefl a b c) = rnf (a, b, c)
  rnf (MyTyConAppCo a b c) = rnf (a, b, c)
  rnf (ForAllCo a b c) = rnf (a, b, c)
  rnf (FunCo a b c d) = rnf (a, b, c, d)

instance NFData Role where
  rnf Nominal = ()
  rnf Representational = ()
  rnf Phantom = ()

instance NFData DataCon where
  rnf (MkData a b c d e f g) = rnf (a, b, c, d, e, f, g)

instance NFData MyTyCon where
  rnf (MyTyCon a b) = rnf (a, b)
