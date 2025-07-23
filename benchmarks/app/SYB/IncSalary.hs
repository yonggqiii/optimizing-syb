{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB.IncSalary (incSalary₂) where

import Data.Company
import Data.Generics

incSalary₂ :: Float -> Company -> Company
incSalary₂ k = everywhere (mkT inc)
  where
    inc :: Salary -> Salary
    inc (S x) = S (x * (1 + k))
