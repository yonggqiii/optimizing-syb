{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB35.RmWeights where

import Data.Tree

class RmWeights a where
  rmWeights₅ :: a -> a

instance RmWeights (WTree Int Int) where
  rmWeights₅ (WithWeight t _) = rmWeights₅ t
  rmWeights₅ (Leaf x) = Leaf x
  rmWeights₅ (Fork l r) = Fork (rmWeights₅ l) (rmWeights₅ r)
