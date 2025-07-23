{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:1000 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYB35Opt.NumTypes (NumTypes' (..)) where

import Data.Data3
import Data.Expr
import Data.List
import Data.Typeable

ntProxy :: Proxy NumTypes'
ntProxy = undefined

go :: Int -> [Int] -> Int
go x [] = x
go x (y : ys) = go x ys + y

class (Data₃ NumTypes' a) => NumTypes' a where
  numTypes₆ :: a -> Int
  numTypes₆ x = go 0 (gmapQ₃ ntProxy numTypes₆ x)

instance NumTypes' Type where
  numTypes₆ x = go 1 (gmapQ₃ ntProxy numTypes₆ x)

instance NumTypes' Integer

instance NumTypes' Expr

instance NumTypes' (Var, Expr)

instance NumTypes' (List' (Var, Expr))

instance NumTypes' Char

instance NumTypes' String'

instance NumTypes' Alt

instance NumTypes' (List' Alt)

instance NumTypes' Var

instance NumTypes' (List' Var)

instance NumTypes' (List' Type)

instance NumTypes' Coercion

instance NumTypes' (List' Coercion)

instance NumTypes' IdDetails

instance NumTypes' ExportFlag

instance NumTypes' IdScope

instance NumTypes' DataCon

instance NumTypes' AltCon

instance NumTypes' Literal

instance NumTypes' Bool

instance NumTypes' Class

instance NumTypes' MyTyCon

instance NumTypes' TyLit

instance NumTypes' Role

instance NumTypes' Bind
