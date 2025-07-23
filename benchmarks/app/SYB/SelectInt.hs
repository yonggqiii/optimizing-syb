{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB.SelectInt where

import Data.Generics
import Data.Tree

selectInt₂ :: WTree Int Int -> [Int]
selectInt₂ = everything (++) ([] `mkQ` (: []))
