{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB35.RenumberInt (renumberInt₅) where

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

renumberInt₅ :: Int -> WTree Int Int -> WTree Int Int
renumberInt₅ x y = evalState (renumberInt₅' y) x

class (Data₃ RenumberInt a) => RenumberInt a where
  renumberInt₅' :: a -> State Int a
  renumberInt₅' = gmapM₃ renumberIntProxy renumberInt₅'

instance RenumberInt Int where
  renumberInt₅' _ = getUnique

instance RenumberInt (WTree Int Int)
