{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYBPEOnly.SelectFloat where

import Data.Company
import Data.Generics

selectFloat₃ :: Company -> [Float]
selectFloat₃ = everything (++) ([] `mkQ` (: []))
