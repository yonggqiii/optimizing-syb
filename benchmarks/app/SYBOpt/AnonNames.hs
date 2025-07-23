{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}

module SYBOpt.AnonNames (anonNames₄) where

import Control.Monad.State.Strict
import Data.Company
import Data.Generics
import Data.List

-------------------------------------------------------------------------------
--
-- The anonNames function anonymizes the names within a company. It does so
-- using the State monad, memoizing the transformation of original names to new
-- anonymized names.
--
-- This is the SYB version of this monadic transformation. anonNamesName
-- expressed the intention of the traversal. The logic of traversing into the
-- data structures is done using `everywhereM`.
--
-- This module should have our optimizations enabled.
--
-------------------------------------------------------------------------------
anonNames₄ :: Company -> Company
anonNames₄ x = evalState (anonNamesCompany x) (1, [])

anonNamesCompany :: Company -> State (Int, [(Name, Name)]) Company
anonNamesCompany = everywhereM (mkM anonNamesName)

anonNamesName :: Name -> State (Int, [(Name, Name)]) Name
anonNamesName n = do
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
