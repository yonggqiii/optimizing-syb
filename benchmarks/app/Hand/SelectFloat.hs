{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.SelectFloat (selectFloat₁) where

import Data.Company
import Data.List

selectFloat₁ :: Company -> [Float]
selectFloat₁ (C c) = selectFloatListDept c

selectFloatListDept :: List' Dept -> [Float]
selectFloatListDept Nil = []
selectFloatListDept (x `Cons` xs) = go [] [selectFloatDept x, selectFloatListDept xs]

selectFloatDept :: Dept -> [Float]
selectFloatDept (D n m ls) = go [] [selectFloatName n, selectFloatEmployee m, selectFloatListSubUnit ls]

selectFloatName :: Name -> [Float]
selectFloatName (MkName n) = selectFloatString n

selectFloatString :: String' -> [Float]
selectFloatString Nil = []
selectFloatString (x `Cons` xs) = go [] [selectFloatChar x, selectFloatString xs]

selectFloatChar :: Char -> [Float]
selectFloatChar _ = []

selectFloatEmployee :: Employee -> [Float]
selectFloatEmployee (E p s) = go [] [selectFloatPerson p, selectFloatSalary s]

selectFloatSalary :: Salary -> [Float]
selectFloatSalary (S x) = [x]

selectFloatPerson :: Person -> [Float]
selectFloatPerson (P n a) = go [] [selectFloatName n, selectFloatString a]

selectFloatListSubUnit :: List' SubUnit -> [Float]
selectFloatListSubUnit Nil = []
selectFloatListSubUnit (x `Cons` xs) = go [] [selectFloatSubUnit x, selectFloatListSubUnit xs]

selectFloatSubUnit :: SubUnit -> [Float]
selectFloatSubUnit (PU e) = selectFloatEmployee e
selectFloatSubUnit (DU d) = selectFloatDept d

go :: [Float] -> [[Float]] -> [Float]
go e [] = e
go e (x : xs) = go (e ++ x) xs
