{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -fexpose-all-unfoldings #-}
module Data.Company where

import Data.Generics

data TreeLike a b = T Company 
                  | T2 a b
                  | T3 [a] [b]
  deriving (Data, Show)


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

  

