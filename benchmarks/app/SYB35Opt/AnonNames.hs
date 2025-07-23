{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin OptimizingSYB #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--iter:100 #-}
{-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--no-symb-exec #-}

module SYB35Opt.AnonNames (anonNames₆) where

import Control.Monad.State.Strict
import Data.Company
import Data.Data3
import Data.List
import Data.Typeable

anonNamesProxy :: Proxy AnonNames
anonNamesProxy = undefined

anonNames₆ :: Company -> Company
anonNames₆ x = evalState (anonNames x) (1, [])

class (Data₃ AnonNames a) => AnonNames a where
  anonNames :: a -> State (Int, [(Name, Name)]) a
  anonNames = gmapM₃ anonNamesProxy anonNames

instance AnonNames Name where
  anonNames n = do
    (ctr, mp) <- get :: State (Int, [(Name, Name)]) (Int, [(Name, Name)])
    case lookup n mp of
      Just x -> return x
      Nothing -> do
        let new_name = MkName (fromNativeList ("anon" ++ show ctr))
        put (ctr + 1, (n, new_name) : mp)
        return new_name

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
