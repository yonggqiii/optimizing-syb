{-# OPTIONS_GHC -O2 -ddump-inlinings -ddump-simpl -ddump-ds -ddump-to-file -fplugin OptimizingSYB #-}
{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Data.Company
import Data.Generics

incS :: Float -> Salary -> Salary
incS k (S s) = S (s * (1 + k))

incNum :: Float -> Int -> Int -> Int
incNum a b c = floor a + b + c


increase :: Data a => Int -> Float -> a -> a
increase a b = everywhere $ mkT (incNum b a)

anotherIncrease :: Data a => Float -> a -> a
anotherIncrease k =
  let f :: forall a. Data a => a -> a 
      f = mkT $ incS k
  in everywhere f 
{-# SPECIALIZE increase :: Int -> Float -> [Dept] -> [Dept] #-}
{-# SPECIALIZE increase :: Int -> Float -> Company -> Company #-}
-- {-# SPECIALIZE increase :: Data a => Float -> [a] -> [a] #-}
 
add' :: Num a => a -> a -> a
add' x y = x + y

{-# SPECIALIZE add' :: Int -> Int -> Int #-}

-- c, d :: Company
-- c = C []
-- d = increase 2 c

-- nonsense :: a -> a
-- nonsense x = x
main :: IO ()
main = do
  putStrLn "Hello, Haskell!"
