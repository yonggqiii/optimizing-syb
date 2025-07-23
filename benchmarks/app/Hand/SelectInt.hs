{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.SelectInt (selectInt₁) where

import Data.Tree

go :: [Int] -> [[Int]] -> [Int]
go e [] = e
go e (x : xs) = go (e ++ x) xs

selectInt₁ :: WTree Int Int -> [Int]
selectInt₁ (Leaf x) = [x]
selectInt₁ (Fork l r) = go [] [selectInt₁ l, selectInt₁ r]
selectInt₁ (WithWeight t w) = go [] [selectInt₁ t, [w]]
