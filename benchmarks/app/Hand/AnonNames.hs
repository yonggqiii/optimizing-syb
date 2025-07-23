{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Hand.AnonNames (anonNames₁) where

import Control.Monad.State.Strict
import Data.Company
import Data.List

-------------------------------------------------------------------------------
--
-- The anonNames function anonymizes the names within a company. It does so
-- using the State monad, memoizing the transformation of original names to new
-- anonymized names.
--
-- This is the "handwritten" version of this monadic transformation. Virtually
-- everything here except 'anonNamesName' is just boilerplate which traverses
-- the data structure.
--
-------------------------------------------------------------------------------

anonNames₁ :: Company -> Company
anonNames₁ x = evalState (anonNamesCompany x) (1, [])

anonNamesCompany :: Company -> State (Int, [(Name, Name)]) Company
anonNamesCompany (C ls) = C <$> anonNamesListDept ls

anonNamesListDept :: List' Dept -> State (Int, [(Name, Name)]) (List' Dept)
anonNamesListDept Nil = return Nil
anonNamesListDept (x `Cons` xs) =
  Cons
    <$> anonNamesDept x
    <*> anonNamesListDept xs

anonNamesDept :: Dept -> State (Int, [(Name, Name)]) Dept
anonNamesDept (D n m s) =
  D
    <$> anonNamesName n
    <*> anonNamesEmployee m
    <*> anonNamesListSubUnit s

-- This is the actual interesting portion of the traversal.
anonNamesName :: Name -> State (Int, [(Name, Name)]) Name
anonNamesName (MkName s) = do
  -- First, recursively anonymize any names occurring in subterms.
  s' <- anonNamesString s
  -- Get the current counter and the memoized mappings.
  (ctr, mp) <- get :: State (Int, [(Name, Name)]) (Int, [(Name, Name)])
  -- Take s' and put it as a Name
  let transformed_name = MkName s'
  -- Check if the transformation on transformed_name has already been done
  -- before.
  case lookup transformed_name mp of
    -- It has been done before, so just use the memoized result.
    Just x -> return x
    Nothing -> do
      -- Create a new unique anonymized name using the counter
      let new_name = MkName (fromNativeList ("anon" ++ show ctr))
      -- Increment the counter and memoize the result in the map
      put (ctr + 1, (transformed_name, new_name) : mp)
      return new_name

anonNamesEmployee :: Employee -> State (Int, [(Name, Name)]) Employee
anonNamesEmployee (E p s) = E <$> anonNamesPerson p <*> anonNamesSalary s

anonNamesPerson :: Person -> State (Int, [(Name, Name)]) Person
anonNamesPerson (P n a) = P <$> anonNamesName n <*> anonNamesString a

anonNamesSalary :: Salary -> State (Int, [(Name, Name)]) Salary
anonNamesSalary (S x) = S <$> anonNamesFloat x

anonNamesFloat :: Float -> State (Int, [(Name, Name)]) Float
anonNamesFloat = return

anonNamesListSubUnit ::
  List' SubUnit ->
  State (Int, [(Name, Name)]) (List' SubUnit)
anonNamesListSubUnit Nil = return Nil
anonNamesListSubUnit (x `Cons` xs) =
  Cons
    <$> anonNamesSubUnit x
    <*> anonNamesListSubUnit xs

anonNamesSubUnit :: SubUnit -> State (Int, [(Name, Name)]) SubUnit
anonNamesSubUnit (PU e) = PU <$> anonNamesEmployee e
anonNamesSubUnit (DU d) = DU <$> anonNamesDept d

anonNamesString :: String' -> State (Int, [(Name, Name)]) String'
anonNamesString Nil = return Nil
anonNamesString (x `Cons` xs) = Cons <$> anonNamesChar x <*> anonNamesString xs

anonNamesChar :: Char -> State (Int, [(Name, Name)]) Char
anonNamesChar = return
