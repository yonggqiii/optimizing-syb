{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:1000 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYBPEOnly.IncInt (incInt₃) where

import Data.Expr
import Data.Generics

add :: Integer -> Integer
add = (+ 1)

incInt₃ :: Expr -> Expr
incInt₃ = everywhere (mkT add)
