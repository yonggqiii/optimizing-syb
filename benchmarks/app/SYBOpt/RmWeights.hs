{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}

module SYBOpt.RmWeights where

import Data.Generics
import Data.Tree

rmWeights₄ :: WTree Int Int -> WTree Int Int
rmWeights₄ = everywhere (mkT rmAdhoc)
  where
    rmAdhoc :: WTree Int Int -> WTree Int Int
    rmAdhoc (WithWeight t _) = t
    rmAdhoc t = t
