{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB.NumTypes (numTypes₂) where

import Data.Expr
import Data.Generics

numTypes₂ :: Expr -> Int
numTypes₂ = everything (+) (0 `mkQ` my_q)

my_q :: Type -> Int
my_q _ = 1
