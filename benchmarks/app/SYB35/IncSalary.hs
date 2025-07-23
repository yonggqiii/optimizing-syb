{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB35.IncSalary where

import Data.Company
import Data.Data3
import Data.List
import Data.Typeable (Proxy)

incProxy :: Proxy IncSalary
incProxy = undefined

class (Data₃ IncSalary a) => IncSalary a where
  incSalary₅ :: Float -> a -> a
  incSalary₅ k = gmapT₃ incProxy (incSalary₅ k)

instance IncSalary Salary where
  incSalary₅ k (S x) = S (x * (1 + k))

instance IncSalary Name

instance IncSalary Company

instance IncSalary Dept

instance IncSalary Char

instance IncSalary String'

instance IncSalary Float

instance IncSalary (List' Dept)

instance IncSalary SubUnit

instance IncSalary (List' SubUnit)

instance IncSalary Person

instance IncSalary Employee
