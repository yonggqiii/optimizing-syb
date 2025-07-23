{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:1000 #-}

module SYBOpt.IncInt (incInt₄) where

import Data.Expr
import Data.Generics

add :: Integer -> Integer
add = (+ 1)

incInt₄ :: Expr -> Expr
incInt₄ = everywhere (mkT add)
