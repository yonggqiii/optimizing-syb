{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:1000 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYB35Opt.IncInt (IncInt' (..)) where

import Data.Data3
import Data.Expr
import Data.List
import Data.Typeable

incIntProxy :: Proxy IncInt'
incIntProxy = undefined

class (Data₃ IncInt' a) => IncInt' a where
  incInt₆ :: a -> a
  incInt₆ = gmapT₃ incIntProxy incInt₆

instance IncInt' Integer where
  incInt₆ = (+ 1)

instance IncInt' Expr

instance IncInt' (Var, Expr)

instance IncInt' (List' (Var, Expr))

instance IncInt' Char

instance IncInt' String'

instance IncInt' Alt

instance IncInt' (List' Alt)

instance IncInt' Var

instance IncInt' (List' Var)

instance IncInt' (List' Type)

instance IncInt' Type

instance IncInt' Coercion

instance IncInt' (List' Coercion)

instance IncInt' IdDetails

instance IncInt' ExportFlag

instance IncInt' IdScope

instance IncInt' DataCon

instance IncInt' AltCon

instance IncInt' Literal

instance IncInt' Bool

instance IncInt' Class

instance IncInt' MyTyCon

instance IncInt' TyLit

instance IncInt' Role

instance IncInt' Bind
