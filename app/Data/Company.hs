{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -fexpose-all-unfoldings #-}
module Data.Company where

import Data.Generics


data Company = C [Dept] 
  deriving (Typeable, Show, Data)

data Dept = D Name Manager [SubUnit] 
  deriving (Typeable, Show, Data)

data SubUnit = PU Employee 
             | DU Dept 
  deriving (Typeable, Show, Data)

data Employee = E Person Salary 
  deriving (Typeable, Show, Data)

data Person = P Name Address 
  deriving (Typeable, Show, Data)

data Salary = S Float 
  deriving (Typeable, Show, Data)

type Manager = Employee
type Name = String
type Address = String

data List a = EmptyList | Cons a (List a)
  deriving (Show, Data)

data Tree a = Leaf a | Tree (Tree a) a (Tree a)
  deriving (Show, Data)

data Wrapper = Wrapper (Tree Int)
  deriving (Show, Data)
