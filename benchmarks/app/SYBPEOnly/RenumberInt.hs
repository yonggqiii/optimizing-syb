{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYBPEOnly.RenumberInt (renumberInt₃) where

import Control.Monad.State.Strict
import Data.Generics
import Data.Tree

getUnique :: State Int Int
getUnique = do
  u <- get
  modify (+ 1)
  return u

renumberInt₃ :: Int -> WTree Int Int -> WTree Int Int
renumberInt₃ x y = evalState (renumberInt₃' y) x

renumberInt₃' :: WTree Int Int -> State Int (WTree Int Int)
renumberInt₃' = everywhereM (mkM m)

m :: Int -> State Int Int
m _ = getUnique
