{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYB35Opt.SelectInt (SelectInt' (..)) where

import Data.Tree

class SelectInt' a where
  selectInt₆ :: a -> [Int]

instance SelectInt' (WTree Int Int) where
  selectInt₆ (Leaf x) = [x]
  selectInt₆ (Fork l r) = go [] [selectInt₆ l, selectInt₆ r]
  selectInt₆ (WithWeight t w) = go [] [selectInt₆ t, [w]]

go :: [Int] -> [[Int]] -> [Int]
go e [] = e
go e (x : xs) = go (e ++ x) xs
