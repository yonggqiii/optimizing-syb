{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB35.SelectInt (SelectInt (..)) where

import Data.Tree

class SelectInt a where
  selectInt₅ :: a -> [Int]

instance SelectInt (WTree Int Int) where
  selectInt₅ (Leaf x) = [x]
  selectInt₅ (Fork l r) = go [] [selectInt₅ l, selectInt₅ r]
  selectInt₅ (WithWeight t w) = go [] [selectInt₅ t, [w]]

go :: [Int] -> [[Int]] -> [Int]
go e [] = e
go e (x : xs) = go (e ++ x) xs
