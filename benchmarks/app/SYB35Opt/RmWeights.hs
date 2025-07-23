{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYB35Opt.RmWeights where

import Data.Tree

class RmWeights' a where
  rmWeights₆ :: a -> a

instance RmWeights' (WTree Int Int) where
  rmWeights₆ (WithWeight t _) = rmWeights₆ t
  rmWeights₆ (Leaf x) = Leaf x
  rmWeights₆ (Fork l r) = Fork (rmWeights₆ l) (rmWeights₆ r)
