{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--debug #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}

module SYBOpt.RenumberInt (renumberInt₄) where

import Control.Monad.State.Strict
import Data.Generics
import Data.Tree

getUnique :: State Int Int
getUnique = do
  u <- get
  modify (+ 1)
  return u

renumberInt₄ :: Int -> WTree Int Int -> WTree Int Int
renumberInt₄ x y = evalState (renumberInt₄' y) x

renumberInt₄' :: WTree Int Int -> State Int (WTree Int Int)
renumberInt₄' = everywhereM (mkM m)

m :: Int -> State Int Int
m _ = getUnique
