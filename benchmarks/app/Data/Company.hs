{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module Data.Company where

import Control.DeepSeq
import Data.Data
import Data.Data3
import Data.List

-------------------------------------------------------------------------------
--
-- Company type definition
--
--   This is (more-or-less) the Company data type shown in the original SYB paper.
--   Some changes include making 'Name' its own data type so that we can perform
--   name changes easily with the original SYB, and letting these types be
--   `newtype`s where possible.
-------------------------------------------------------------------------------

newtype Company = C (List' Dept) deriving (Show, Data, Eq)

data Dept = D Name Manager (List' SubUnit) deriving (Show, Data, Eq)

data SubUnit = PU Employee | DU Dept deriving (Show, Data, Eq)

data Employee = E Person Salary deriving (Show, Data, Eq)

data Person = P Name Address deriving (Show, Data, Eq)

newtype Salary = S Float deriving (Show, Data, Eq)

newtype Name = MkName String' deriving (Show, Data, Eq)

type Manager = Employee

type Address = String'

-------------------------------------------------------------------------------
--
-- Data₃ instances for SYB3.5
--
-------------------------------------------------------------------------------
instance
  ( γ (List' Dept),
    γ Company,
    γ Dept,
    γ Person,
    γ Salary,
    γ Employee,
    γ Float,
    γ Char,
    γ String',
    γ SubUnit,
    γ (List' SubUnit),
    γ Name
  ) =>
  Data₃ γ Company
  where
  gmapT₃ _ f (C x) = C (f x)
  gmapQ₃ _ f (C x) = [f x]
  gmapM₃ _ f (C x) = C <$> f x

instance (γ Float, γ Salary, γ Name) => Data₃ γ Salary where
  gmapT₃ _ f (S x) = S (f x)
  gmapQ₃ _ f (S x) = [f x]
  gmapM₃ _ f (S x) = S <$> f x

instance (γ Char, γ String', γ Person, γ Name) => Data₃ γ Person where
  gmapT₃ _ f (P n a) = P (f n) (f a)
  gmapQ₃ _ f (P n a) = [f n, f a]
  gmapM₃ _ f (P n a) = do
    n' <- f n
    a' <- f a
    return $ P n' a'

instance
  ( γ Person,
    γ Salary,
    γ Employee,
    γ Float,
    γ Char,
    γ String',
    γ Name
  ) =>
  Data₃ γ Employee
  where
  gmapT₃ _ f (E p s) = E (f p) (f s)
  gmapQ₃ _ f (E p s) = [f p, f s]
  gmapM₃ _ f (E p s) = do
    p' <- f p
    s' <- f s
    return $ E p' s'

instance
  ( γ Person,
    γ Salary,
    γ Employee,
    γ Float,
    γ Char,
    γ String',
    γ SubUnit,
    γ (List' SubUnit),
    γ Dept,
    γ Name
  ) =>
  Data₃ γ SubUnit
  where
  gmapT₃ _ f (PU e) = PU (f e)
  gmapT₃ _ f (DU d) = DU (f d)
  gmapQ₃ _ f (PU e) = [f e]
  gmapQ₃ _ f (DU d) = [f d]
  gmapM₃ _ f (PU e) = PU <$> f e
  gmapM₃ _ f (DU e) = DU <$> f e

instance
  ( γ Person,
    γ Salary,
    γ Employee,
    γ Float,
    γ Char,
    γ String',
    γ Dept,
    γ (List' SubUnit),
    γ SubUnit,
    γ Name
  ) =>
  Data₃ γ Dept
  where
  gmapT₃ _ f (D n m s) = D (f n) (f m) (f s)
  gmapQ₃ _ f (D n m s) = [f n, f m, f s]
  gmapM₃ _ f (D n m s) = do
    n' <- f n
    m' <- f m
    s' <- f s
    return $ D n' m' s'

instance (γ Name, γ String', γ Char) => Data₃ γ Name where
  gmapT₃ _ f (MkName n) = MkName (f n)
  gmapQ₃ _ f (MkName n) = [f n]
  gmapM₃ _ f (MkName n) = MkName <$> f n

-------------------------------------------------------------------------------
--
-- NFData instances for benchmarking to normal form.
--
-------------------------------------------------------------------------------

instance NFData Company where
  rnf (C x) = rnf x

instance NFData Dept where
  rnf (D n m s) = rnf (n, m, s)

instance NFData SubUnit where
  rnf (PU e) = rnf e
  rnf (DU d) = rnf d

instance NFData Employee where
  rnf (E p s) = rnf (p, s)

instance NFData Person where
  rnf (P n a) = rnf (n, a)

instance NFData Salary where
  rnf (S s) = rnf s

instance NFData Name where
  rnf (MkName n) = rnf n

-------------------------------------------------------------------------------
--
-- Convenience functions for creating companies
--
-------------------------------------------------------------------------------

mkCompany :: Int -> Company
mkCompany 0 = C Nil
mkCompany n = C (fromNativeList (replicate n (mkDept (n - 1))))

mkDept :: Int -> Dept
mkDept 0 = D (MkName $ fromNativeList "name0") (mkEmployee 0) Nil
mkDept n =
  D
    (MkName $ fromNativeList ("name" ++ show n))
    (mkEmployee (n - 1))
    (fromNativeList (replicate n (mkSubUnit (n - 1))))

mkEmployee :: Int -> Employee
mkEmployee n =
  E
    ( P
        (MkName $ fromNativeList ("name" ++ show n))
        (fromNativeList "addr")
    )
    (S 10.0)

mkSubUnit :: Int -> SubUnit
mkSubUnit 0 = PU (mkEmployee 0)
mkSubUnit n = if even n then PU (mkEmployee 0) else DU (mkDept (n - 1))
