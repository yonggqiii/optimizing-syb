{-# OPTIONS_GHC -O2 -ddump-inlinings -ddump-simpl -ddump-ds -ddump-to-file -fplugin OptimizingSYB #-}
{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Data.Company
import Data.Generics

incS :: Float -> Salary -> Salary
incS k (S s) = S (s * (1 + k))

incNum :: Float -> Int -> Int -> Int
incNum a b c = floor a + b + c


increase :: Data a => Float -> a -> a
increase k = everywhere $ mkT (incS k)

-- anotherIncrease :: Data a => Float -> a -> a
-- anotherIncrease k =
--   let f :: forall a. Data a => a -> a 
--       f = mkT $ incS k
--   in everywhere f 
{-# SPECIALIZE increase :: Float -> [Dept] -> [Dept] #-}
{-# SPECIALIZE increase :: Float -> Company -> Company #-}
-- {-# SPECIALIZE increase :: Data a => Float -> [a] -> [a] #-}
 
-- add' :: Num a => a -> a -> a
-- add' x y = x + y
--
-- {-# SPECIALIZE add' :: Int -> Int -> Int #-}

-- c, d :: Company
-- c = C []
-- d = increase 2 c

-- nonsense :: a -> a
-- nonsense x = x
main :: IO ()
main = do
  let p1 = P "Alice" ""
  let p2 = P "Bob" ""
  let p3 = P "Charlie" ""
  let e1 = E p1 $ S 1000
  let e2 = E p2 $ S 2000
  let e3 = E p3 $ S 3000
  let d1 = D "Alice's place" e1 []
  let d2 = D "Bob's place" e2 [PU e3]
  let c = C [d1, d2]
  print c
  let d = increase 0.1 c
  print d
  return ()
