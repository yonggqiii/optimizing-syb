{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--debug #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}

module SYB35Opt.SelectFloat (SelectFloat' (..)) where

import Data.Company
import Data.Data3
import Data.List
import Data.Typeable (Proxy)

sfProxy :: Proxy SelectFloat'
sfProxy = undefined

go :: [Float] -> [[Float]] -> [Float]
go e [] = e
go e (x : xs) = go (e ++ x) xs

class (Data₃ SelectFloat' a) => SelectFloat' a where
  selectFloat₆ :: a -> [Float]
  selectFloat₆ x = go [] (gmapQ₃ sfProxy selectFloat₆ x)

instance SelectFloat' Salary where
  selectFloat₆ (S x) = [x]

instance SelectFloat' Company

instance SelectFloat' Dept

instance SelectFloat' Name

instance SelectFloat' Char

instance SelectFloat' String'

instance SelectFloat' Float

instance SelectFloat' (List' Dept)

instance SelectFloat' SubUnit

instance SelectFloat' (List' SubUnit)

instance SelectFloat' Person

instance SelectFloat' Employee
