{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:1000 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYB35Opt.DropCasts (dropCasts₆) where

import Control.Monad.Writer.Strict
import Data.Data3
import Data.Expr
import Data.List
import Data.Monoid (Sum (..), getSum)
import Data.Typeable

dropCasts₆ :: Expr -> (Expr, Int)
dropCasts₆ x = let (a, b) = runWriter (dropCasts x) in (a, getSum b)

dropCastsProxy :: Proxy DropCasts
dropCastsProxy = undefined

class (Data₃ DropCasts a) => DropCasts a where
  dropCasts :: a -> Writer (Sum Int) a
  dropCasts = gmapM₃ dropCastsProxy dropCasts

instance DropCasts Expr where
  dropCasts (Cast e _) = do
    tell (Sum 1)
    dropCasts e
  dropCasts x = gmapM₃ dropCastsProxy dropCasts x

instance DropCasts Type where
  dropCasts (CastTy t _) = do
    tell (Sum 1)
    dropCasts t
  dropCasts x = gmapM₃ dropCastsProxy dropCasts x

instance DropCasts String'

instance DropCasts Char

instance DropCasts Integer

instance DropCasts (Var, Expr)

instance DropCasts (List' (Var, Expr))

instance DropCasts Alt

instance DropCasts (List' Alt)

instance DropCasts Var

instance DropCasts (List' Var)

instance DropCasts (List' Type)

instance DropCasts Coercion

instance DropCasts (List' Coercion)

instance DropCasts IdDetails

instance DropCasts ExportFlag

instance DropCasts IdScope

instance DropCasts DataCon

instance DropCasts AltCon

instance DropCasts Literal

instance DropCasts Bool

instance DropCasts Class

instance DropCasts MyTyCon

instance DropCasts TyLit

instance DropCasts Role

instance DropCasts Bind
