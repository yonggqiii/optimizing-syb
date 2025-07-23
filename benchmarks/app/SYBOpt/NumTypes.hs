{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--debug #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:1000 #-}

module SYBOpt.NumTypes (numTypes₄) where

import Data.Expr
import Data.Generics

numTypes₄ :: Expr -> Int
numTypes₄ = everything (+) (0 `mkQ` myQ)

myQ :: Type -> Int
myQ _ = 1
