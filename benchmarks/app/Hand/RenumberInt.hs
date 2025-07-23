{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.RenumberInt (renumberInt₁) where

import Control.Monad.State.Strict
import Data.Tree

getUnique :: State Int Int
getUnique = do
  u <- get
  modify (+ 1)
  return u

renumberInt₁ :: Int -> WTree Int Int -> WTree Int Int
renumberInt₁ x y = evalState (renumberInt₁' y) x

renumberInt₁' :: WTree Int Int -> State Int (WTree Int Int)
renumberInt₁' (Leaf _) = Leaf <$> getUnique
renumberInt₁' (Fork l r) = do
  l' <- renumberInt₁' l
  r' <- renumberInt₁' r
  return $ Fork l' r'
renumberInt₁' (WithWeight l _) = do
  l' <- renumberInt₁' l
  WithWeight l' <$> getUnique
