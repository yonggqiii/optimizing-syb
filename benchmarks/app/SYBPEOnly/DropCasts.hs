{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:1000 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYBPEOnly.DropCasts (dropCasts₃) where

import Control.Monad.Writer.Strict
import Data.Expr
import Data.Generics
import Data.Monoid (Sum (..), getSum)

dropCasts₃ :: Expr -> (Expr, Int)
dropCasts₃ x = let (a, b) = runWriter (dropCasts x) in (a, getSum b)

dropCasts :: Expr -> Writer (Sum Int) Expr
dropCasts = everywhereM (return `extM` myExprTrans `extM` myTypeTrans)

myExprTrans :: Expr -> Writer (Sum Int) Expr
myExprTrans (Cast e _) = do
  tell (Sum 1)
  return e
myExprTrans x = return x

myTypeTrans :: Type -> Writer (Sum Int) Type
myTypeTrans (CastTy t _) = do
  tell (Sum 1)
  return t
myTypeTrans x = return x
