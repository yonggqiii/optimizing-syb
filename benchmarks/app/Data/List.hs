{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

-- | This module is to replace the native lists in Haskell so that the Data
-- unfoldings can be exposed.
module Data.List where

import Control.DeepSeq
import Data.Data
import Data.Data3

-------------------------------------------------------------------------------
--
-- Our own List datatype
--
--   The reason this type exists is so that we can expose all unfoldings of the
--   Data instances, which the native lists of GHC do not do. An alternative
--   solution is to re-compile the GHC base library with the option
--   -fexpose-all-unfoldings like we have done above; however, for simplicity
--   of reproducibility, we opt for this solution instead.
--
--   Most notably, this List type is only used within the types being traversed
--   by our benchmark programs. The Data and Data₃ instances still make use of
--   the native list type [], so that we are still able to observe the effects
--   of GHC's optimizations on [], such as deforestation.
--
-------------------------------------------------------------------------------
data List' α = Nil | Cons α (List' α)
  deriving (Data, Eq)

instance (Show α) => Show (List' α) where
  show = show . toNativeList

instance (γ (List' α), Data₃ γ α) => Data₃ γ (List' α) where
  gmapT₃ _ _ Nil = Nil
  gmapT₃ _ f (Cons x xs) = Cons (f x) (f xs)
  gmapQ₃ _ _ Nil = []
  gmapQ₃ _ f (Cons x xs) = [f x, f xs]
  gmapM₃ _ _ Nil = return Nil
  gmapM₃ _ f (Cons x xs) = do
    x' <- f x
    xs' <- f xs
    return $ Cons x' xs'

instance Foldable List' where
  foldr f y = go
    where
      go Nil = y
      go (Cons x xs) = f x (go xs)

type String' = List' Char

fromNativeList :: forall α. [α] -> List' α
fromNativeList = foldr Cons Nil

toNativeList :: forall α. List' α -> [α]
toNativeList = foldr (:) []

instance Functor List' where
  fmap _ Nil = Nil
  fmap f (x `Cons` xs) = f x `Cons` fmap f xs

instance (NFData α) => NFData (List' α) where
  rnf Nil = ()
  rnf (Cons x xs) = rnf (x, xs)
