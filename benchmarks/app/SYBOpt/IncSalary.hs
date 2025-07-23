{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--debug #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}

module SYBOpt.IncSalary (incSalary₄) where

import Data.Company
import Data.Generics

incSalary₄ :: Float -> Company -> Company
incSalary₄ k = everywhere (mkT inc)
  where
    inc :: Salary -> Salary
    inc (S x) = S (x * (1 + k))
