{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module Data.Tree where

import Control.DeepSeq
import Data.Data3
import Data.Generics

-------------------------------------------------------------------------------
--
-- Weighted trees, taken from GPBench.
--
-------------------------------------------------------------------------------

data WTree α ω
  = Leaf α
  | Fork (WTree α ω) (WTree α ω)
  | WithWeight (WTree α ω) ω
  deriving (Show, Data, Eq)

-------------------------------------------------------------------------------
--
-- Data₃ instances for WTree
--
-------------------------------------------------------------------------------

instance (Data₃ γ α, Data₃ γ β, γ (WTree α β)) => Data₃ γ (WTree α β) where
  gmapT₃ _ f (Leaf a) = Leaf (f a)
  gmapT₃ _ f (Fork x y) = Fork (f x) (f y)
  gmapT₃ _ f (WithWeight x y) = WithWeight (f x) (f y)
  gmapQ₃ _ f (Leaf a) = [f a]
  gmapQ₃ _ f (Fork a b) = [f a, f b]
  gmapQ₃ _ f (WithWeight x y) = [f x, f y]
  gmapM₃ _ f (Leaf a) = do
    a' <- f a
    return $ Leaf a'
  gmapM₃ _ f (Fork a b) = do
    a' <- f a
    b' <- f b
    return $ Fork a' b'
  gmapM₃ _ f (WithWeight a b) = do
    a' <- f a
    b' <- f b
    return $ WithWeight a' b'

-------------------------------------------------------------------------------
--
-- NFData instances for WTrees
--
-------------------------------------------------------------------------------

instance (NFData α, NFData β) => NFData (WTree α β) where
  rnf (Leaf a) = rnf a
  rnf (Fork l r) = rnf (l, r)
  rnf (WithWeight t w) = rnf (t, w)

-------------------------------------------------------------------------------
--
-- Convenience functions for creating WTrees.
--
-------------------------------------------------------------------------------

mkWTree :: Int -> WTree Int Int
mkWTree n
  | n <= 1 = Leaf n
  | even n = WithWeight (mkWTree (div n 2)) n
  | otherwise = Fork (mkWTree (3 * n + 1)) (mkWTree (n - 1))

powerOfTwo :: Int -> WTree a w -> WTree a w
powerOfTwo 0 t = t
powerOfTwo n t = Fork (powerOfTwo (n - 1) t) (powerOfTwo (n - 1) t)

onewtree :: WTree Int Int
onewtree = mkWTree 15

bigwtree :: Int -> WTree Int Int
bigwtree n = powerOfTwo n onewtree
