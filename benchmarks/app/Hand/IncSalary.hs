{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.IncSalary (incSalary₁) where

import Data.Company
import Data.List

incSalary₁ :: Float -> Company -> Company
incSalary₁ x (C e) = C $ incSalaryListDept x e

incSalaryListDept :: Float -> List' Dept -> List' Dept
incSalaryListDept x = (incSalaryDept x <$>)

incSalaryDept :: Float -> Dept -> Dept
incSalaryDept x (D n m ls) = D (incSalaryName x n) (incSalaryEmployee x m) (incSalaryListSubUnit x ls)

incSalaryEmployee :: Float -> Employee -> Employee
incSalaryEmployee x (E p s) = E (incSalaryPerson x p) (incSalarySalary x s)

incSalaryPerson :: Float -> Person -> Person
incSalaryPerson k (P n a) = P (incSalaryName k n) (incSalaryString k a)

incSalaryName :: Float -> Name -> Name
incSalaryName k (MkName n) = MkName (incSalaryString k n)

incSalarySalary :: Float -> Salary -> Salary
incSalarySalary x (S s) = S (s * (1 + x))

incSalaryListSubUnit :: Float -> List' SubUnit -> List' SubUnit
incSalaryListSubUnit x = (incSalarySubUnit x <$>)

incSalarySubUnit :: Float -> SubUnit -> SubUnit
incSalarySubUnit x (PU e) = PU $ incSalaryEmployee x e
incSalarySubUnit x (DU e) = DU $ incSalaryDept x e

incSalaryString :: Float -> String' -> String'
incSalaryString _ Nil = Nil
incSalaryString k (x `Cons` xs) = Cons x (incSalaryString k xs)
