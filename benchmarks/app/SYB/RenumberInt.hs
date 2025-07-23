{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB.RenumberInt (renumberInt₂) where

import Control.Monad.State.Strict
import Data.Generics
import Data.Tree

getUnique :: State Int Int
getUnique = do
  u <- get
  modify (+ 1)
  return u

renumberInt₂ :: Int -> WTree Int Int -> WTree Int Int
renumberInt₂ x y = evalState (renumberInt₂' y) x

renumberInt₂' :: WTree Int Int -> State Int (WTree Int Int)
renumberInt₂' = everywhereM (mkM m)

m :: Int -> State Int Int
m _ = getUnique
