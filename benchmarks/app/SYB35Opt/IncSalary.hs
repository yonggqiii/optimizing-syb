{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYB35Opt.IncSalary where

import Data.Company
import Data.Data3
import Data.List
import Data.Typeable (Proxy)

incProxy :: Proxy IncSalary'
incProxy = undefined

class (Data₃ IncSalary' a) => IncSalary' a where
  incSalary₆ :: Float -> a -> a
  incSalary₆ k = gmapT₃ incProxy (incSalary₆ k)

instance IncSalary' Salary where
  incSalary₆ k (S x) = S (x * (1 + k))

instance IncSalary' Company

instance IncSalary' Dept

instance IncSalary' Name

instance IncSalary' Char

instance IncSalary' String'

instance IncSalary' Float

instance IncSalary' (List' Dept)

instance IncSalary' SubUnit

instance IncSalary' (List' SubUnit)

instance IncSalary' Person

instance IncSalary' Employee
