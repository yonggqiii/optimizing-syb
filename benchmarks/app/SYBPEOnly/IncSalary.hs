{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYBPEOnly.IncSalary (incSalary₃) where

import Data.Company
import Data.Generics

incSalary₃ :: Float -> Company -> Company
incSalary₃ k = everywhere (mkT inc)
  where
    inc :: Salary -> Salary
    inc (S x) = S (x * (1 + k))
