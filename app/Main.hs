{-# OPTIONS_GHC -O2 -ddump-inlinings -ddump-simpl -ddump-ds -ddump-to-file -fplugin OptimizingSYB #-}
-- {-# OPTIONS_GHC -O2 #-}
-- {-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-simple #-}
-- {-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-function-map #-}
-- {-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-traversal-extraction #-}
-- {-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-scheme-elim #-}
-- {-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-spec #-}
-- {-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-gmap-elim #-}
-- {-# OPTIONS_GHC -fplugin-opt OptimizingSYB:--show-type-eval #-}
{-# LANGUAGE UnicodeSyntax #-}
module Main where

import Data.Company
import Data.Generics

-- data Company = C [Dept] 
--   deriving (Typeable, Show, Data)
--
-- data Dept = D Name Manager [SubUnit] 
--   deriving (Typeable, Show, Data)
--
-- data SubUnit = PU Employee 
--              | DU Dept 
--   deriving (Typeable, Show, Data)
--
-- data Employee = E Person Salary 
--   deriving (Typeable, Show, Data)
--
-- data Person = P Name Address 
--   deriving (Typeable, Show, Data)
--
-- data Salary = S Float 
--   deriving (Typeable, Show, Data)
--
-- type Manager = Employee
-- type Name = String
-- type Address = String
--
-- data List a = EmptyList | Cons a (List a)
--   deriving (Typeable, Show, Data)


-- incS :: Float -> Salary -> Salary
-- incS k (S s) = S (s * (1 + k))
-- increase :: Float -> Company -> Company
-- increase :: Data a => Float -> a -> a
-- increase k = everywhere' $ mkT (incS k)
-- {-# SPECIALIZE increase :: Data a => Float -> [a] -> [a] #-}
-- incSM :: Float -> Salary -> IO Salary
-- incSM k (S s) = do
--   let new_s = s * (1 + k)
--   putStrLn $ "Increasing salary from " ++ (show s) ++ " to " ++ (show new_s)
--   return $ S new_s

-- increaseM :: Float -> Company -> IO Company
-- increaseM k = everywhereM $ mkM (incSM k)

getS :: Salary -> Float
getS (S s) = s

totalSalary :: Company -> Float
totalSalary = everything (+) $ mkQ 0 getS

-- anotherIncrease :: Data a => Float -> a -> a
-- anotherIncrease k =
--   let f :: forall a. Data a => a -> a 
--       f = mkT $ incS k
--   in everywhere f 
-- {-# SPECIALIZE increase :: Float -> List Dept -> List Dept #-}
-- {-# SPECIALIZE increase :: Float -> Company -> Company #-}
-- {-# SPECIALIZE increase :: Float -> TreeLike Company Int -> TreeLike Company Int #-}
-- {-# SPECIALIZE increase :: Float -> [Dept] -> [Dept] #-}
-- {-# SPECIALIZE increase :: Float -> Employee -> Employee #-}
-- {-# SPECIALIZE increase :: Data a => Float -> [a] -> [a] #-}
-- {-# SPECIALIZE totalSalary :: Company -> Float #-}
 
-- add' :: Num a => a -> a -> a
-- add' x y = x + y
--
-- {-# SPECIALIZE add' :: Int -> Int -> Int #-}

-- c, d :: Company
-- c = C []
-- d = increase 2 c

-- nonsense :: a -> a
-- nonsense x = x

-- addOne :: Int -> Int
-- addOne = (+) 1
--
-- addOneEverywhere :: Wrapper -> Wrapper
-- addOneEverywhere = everywhere $ mkT addOne
--
-- treeTotal :: Wrapper -> Int
-- treeTotal = everything (+) $ mkQ 0 (id :: Int -> Int)

main :: IO ()
main = do
  -- let p1 = P "Alice" ""
  -- let p2 = P "Bob" ""
  -- let p3 = P "Charlie" ""
  -- let e1 = E p1 $ S 1000
  -- let e2 = E p2 $ S 2000
  -- let e3 = E p3 $ S 3000
  -- let d1 = D "Alice's place" e1 []
  -- let d2 = D "Bob's place" e2 [PU e3]
  -- let c = C [d1, d2]
  -- let c = Cons d1 (Cons d2 EmptyList)
  -- print c
  -- new_c <- increaseM 0.1 c
  -- print new_c
  -- let d = increase 0.1 c
  -- print d
  -- print $ totalSalary c
  -- let myTree = Wrapper $ Tree (Leaf 1) 2 (Leaf 3)
  -- print $ addOneEverywhere myTree 
  -- print $ treeTotal $ addOneEverywhere myTree
  return ()
