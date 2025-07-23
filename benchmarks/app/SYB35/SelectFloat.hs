{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB35.SelectFloat (SelectFloat (..)) where

import Data.Company
import Data.Data3
import Data.List
import Data.Typeable (Proxy)

sfProxy :: Proxy SelectFloat
sfProxy = undefined

class (Data₃ SelectFloat a) => SelectFloat a where
  selectFloat₅ :: a -> [Float]
  selectFloat₅ x = go [] (gmapQ₃ sfProxy selectFloat₅ x)

go :: [Float] -> [[Float]] -> [Float]
go e [] = e
go e (x : xs) = go (e ++ x) xs

instance SelectFloat Name

instance SelectFloat Salary where
  selectFloat₅ (S x) = [x]

instance SelectFloat Company

instance SelectFloat Dept

instance SelectFloat Char

instance SelectFloat String'

instance SelectFloat Float

instance SelectFloat (List' Dept)

instance SelectFloat SubUnit

instance SelectFloat (List' SubUnit)

instance SelectFloat Person

instance SelectFloat Employee
