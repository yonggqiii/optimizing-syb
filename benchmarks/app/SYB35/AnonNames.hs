{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module SYB35.AnonNames (anonNames₅) where

import Control.Monad.State.Strict
import Data.Company
import Data.Data3
import Data.List
import Data.Typeable

-------------------------------------------------------------------------------
--
-- The anonNames function anonymizes the names within a company. It does so
-- using the State monad, memoizing the transformation of original names to new
-- anonymized names.
--
-- This is the SYB3.5 version of this monadic transformation. the anonNames
-- method definition for AnonNames Name describes the actual intention of the
-- traversal.
--
-------------------------------------------------------------------------------
anonNamesProxy :: Proxy AnonNames
anonNamesProxy = undefined

anonNames₅ :: Company -> Company
anonNames₅ x = evalState (anonNames x) (1, [])

class (Data₃ AnonNames a) => AnonNames a where
  anonNames :: a -> State (Int, [(Name, Name)]) a
  anonNames = gmapM₃ anonNamesProxy anonNames

instance AnonNames Name where
  anonNames n = do
    -- Get the current counter and the memoized mappings.
    (ctr, mp) <- get :: State (Int, [(Name, Name)]) (Int, [(Name, Name)])
    -- Check if the transformation on transformed_name has already been done
    -- before.
    case lookup n mp of
      -- It has been done before, so just use the memoized result.
      Just x -> return x
      Nothing -> do
        -- Create a new unique anonymized name using the counter
        let new_name = MkName (fromNativeList ("anon" ++ show ctr))
        -- Increment the counter and memoize the result in the map
        put (ctr + 1, (n, new_name) : mp)
        return new_name

-------------------------------------------------------------------------------
--
-- We specify all other instances so we do not have to rely on the
-- OverlappingInstances language extension.
--
-------------------------------------------------------------------------------

instance AnonNames Company

instance AnonNames String'

instance AnonNames Char

instance AnonNames Float

instance AnonNames Salary

instance AnonNames Employee

instance AnonNames Dept

instance AnonNames (List' Dept)

instance AnonNames SubUnit

instance AnonNames (List' SubUnit)

instance AnonNames Person
