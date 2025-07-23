{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:1000 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYBPEOnly.NumTypes (numTypes₃) where

import Data.Expr
import Data.Generics

numTypes₃ :: Expr -> Int
numTypes₃ = everything (+) (0 `mkQ` my_q)

my_q :: Type -> Int
my_q _ = 1
