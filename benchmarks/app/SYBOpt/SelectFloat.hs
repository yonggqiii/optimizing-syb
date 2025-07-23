{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--debug #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}

module SYBOpt.SelectFloat where

import Data.Company
import Data.Generics

selectFloat₄ :: Company -> [Float]
selectFloat₄ = everything (++) ([] `mkQ` (: []))
