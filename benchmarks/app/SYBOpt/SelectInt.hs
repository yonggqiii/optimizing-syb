{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}

module SYBOpt.SelectInt where

import Data.Generics
import Data.Tree

selectInt₄ :: WTree Int Int -> [Int]
selectInt₄ = everything (++) ([] `mkQ` (: []))
