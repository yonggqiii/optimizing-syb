{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.RmWeights where

import Data.Tree

rmWeights₁ :: WTree Int Int -> WTree Int Int
rmWeights₁ (WithWeight t _) = rmWeights₁ t
rmWeights₁ (Leaf x) = Leaf x
rmWeights₁ (Fork l r) = Fork (rmWeights₁ l) (rmWeights₁ r)
