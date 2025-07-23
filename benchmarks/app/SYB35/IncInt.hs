{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB35.IncInt (IncInt (..)) where

import Data.Data3
import Data.Expr
import Data.List
import Data.Typeable

incIntProxy :: Proxy IncInt
incIntProxy = undefined

class (Data₃ IncInt a) => IncInt a where
  incInt₅ :: a -> a
  incInt₅ = gmapT₃ incIntProxy incInt₅

instance IncInt Integer where
  incInt₅ = (+ 1)

instance IncInt Expr

instance IncInt (Var, Expr)

instance IncInt (List' (Var, Expr))

instance IncInt Char

instance IncInt String'

instance IncInt Alt

instance IncInt (List' Alt)

instance IncInt Var

instance IncInt (List' Var)

instance IncInt (List' Type)

instance IncInt Type

instance IncInt Coercion

instance IncInt (List' Coercion)

instance IncInt IdDetails

instance IncInt ExportFlag

instance IncInt IdScope

instance IncInt DataCon

instance IncInt AltCon

instance IncInt Literal

instance IncInt Bool

instance IncInt Class

instance IncInt MyTyCon

instance IncInt TyLit

instance IncInt Role

instance IncInt Bind
