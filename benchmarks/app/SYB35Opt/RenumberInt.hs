{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYB35Opt.RenumberInt (renumberInt₆) where

import Control.Monad.State.Strict
import Data.Data3
import Data.Tree
import Data.Typeable

getUnique :: State Int Int
getUnique = do
  u <- get
  modify (+ 1)
  return u

renumberIntProxy :: Proxy RenumberInt
renumberIntProxy = undefined

renumberInt₆ :: Int -> WTree Int Int -> WTree Int Int
renumberInt₆ x y = evalState (renumberInt₆' y) x

class (Data₃ RenumberInt a) => RenumberInt a where
  renumberInt₆' :: a -> State Int a
  renumberInt₆' = gmapM₃ renumberIntProxy renumberInt₆'

instance RenumberInt Int where
  renumberInt₆' _ = getUnique

instance RenumberInt (WTree Int Int)
