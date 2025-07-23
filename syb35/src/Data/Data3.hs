{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}

module Data.Data3 (Data₃ (..)) where

import Data.List.NonEmpty
import Data.Typeable (Proxy)

class (γ α) => Data₃ γ α where
  gmapT₃ :: Proxy γ -> (forall β. (Data₃ γ β) => β -> β) -> α -> α
  gmapQ₃ :: Proxy γ -> (forall β. (Data₃ γ β) => β -> ρ) -> α -> [ρ]
  gmapM₃ :: Proxy γ -> (Monad μ) => (forall β. (Data₃ γ β) => β -> μ β) -> α -> μ α

-- Basic instances
instance (γ Int) => Data₃ γ Int where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ Float) => Data₃ γ Float where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ Bool) => Data₃ γ Bool where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ Char) => Data₃ γ Char where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ [α], Data₃ γ α) => Data₃ γ [α] where
  gmapT₃ _ _ [] = []
  gmapT₃ _ f (x : xs) = f x : f xs
  gmapQ₃ _ _ [] = []
  gmapQ₃ _ f (x : xs) = [f x, f xs]
  gmapM₃ _ _ [] = return []
  gmapM₃ _ f (x : xs) = do
    x' <- f x
    xs' <- f xs
    return $ x' : xs'

instance (ctx Integer) => Data₃ ctx Integer where
  gmapT₃ _ _ x = x
  gmapQ₃ _ _ _ = []
  gmapM₃ _ _ = return

instance (γ (NonEmpty α), Data₃ γ α, γ [α]) => Data₃ γ (NonEmpty α) where
  gmapT₃ _ f (x :| xs) = f x :| f xs
  gmapQ₃ _ f (x :| xs) = [f x, f xs]
  gmapM₃ _ f (x :| xs) = do
    x' <- f x
    xs' <- f xs
    return $ x' :| xs'

instance (γ (Maybe α), Data₃ γ α) => Data₃ γ (Maybe α) where
  gmapT₃ _ _ Nothing = Nothing
  gmapT₃ _ f (Just x) = Just $ f x
  gmapQ₃ _ _ Nothing = []
  gmapQ₃ _ f (Just x) = [f x]
  gmapM₃ _ _ Nothing = return Nothing
  gmapM₃ _ f (Just x) = Just <$> f x

instance (ctx (alp, bet), Data₃ ctx alp, Data₃ ctx bet) => Data₃ ctx (alp, bet) where
  gmapT₃ _ f (x, y) = (f x, f y)
  gmapQ₃ _ f (x, y) = [f x, f y]
  gmapM₃ _ f (x, y) = (,) <$> f x <*> f y

-- -- | @since base-4.0.0.0
-- deriving instance Data Ordering
--
-- -- | @since base-4.0.0.0
-- deriving instance (Data a, Data b) => Data (Either a b)
--
-- -- | @since base-4.8.0.0
-- deriving instance Data Void
--
-- -- | @since base-4.0.0.0
-- deriving instance Data ()
--
-- -- | @since base-4.15
-- deriving instance Data a => Data (Solo a)
--
-- -- | @since base-4.0.0.0
-- deriving instance (Data a, Data b) => Data (a,b)
--
-- -- | @since base-4.0.0.0
-- deriving instance (Data a, Data b, Data c) => Data (a,b,c)
--
-- -- | @since base-4.0.0.0
-- deriving instance (Data a, Data b, Data c, Data d)
--          => Data (a,b,c,d)
--
-- -- | @since base-4.0.0.0
-- deriving instance (Data a, Data b, Data c, Data d, Data e)
--          => Data (a,b,c,d,e)
--
-- -- | @since base-4.0.0.0
-- deriving instance (Data a, Data b, Data c, Data d, Data e, Data f)
--          => Data (a,b,c,d,e,f)
--
-- -- | @since base-4.0.0.0
-- deriving instance (Data a, Data b, Data c, Data d, Data e, Data f, Data g)
--          => Data (a,b,c,d,e,f,g)
--
-- ------------------------------------------------------------------------------
--
-- -- | @since base-4.8.0.0
-- instance Data a => Data (Ptr a) where
--   toConstr _   = errorWithoutStackTrace "GHC.Internal.Data.Data.toConstr(Ptr)"
--   gunfold _ _  = errorWithoutStackTrace "GHC.Internal.Data.Data.gunfold(Ptr)"
--   dataTypeOf _ = mkNoRepType "GHC.Ptr.Ptr"
--   dataCast1 x  = gcast1 x
--
-- -- | @since base-4.18.0.0
-- deriving instance Data a => Data (ConstPtr a)
--
-- ------------------------------------------------------------------------------
--
-- -- | @since base-4.8.0.0
-- instance Data a => Data (ForeignPtr a) where
--   toConstr _   = errorWithoutStackTrace "GHC.Internal.Data.Data.toConstr(ForeignPtr)"
--   gunfold _ _  = errorWithoutStackTrace "GHC.Internal.Data.Data.gunfold(ForeignPtr)"
--   dataTypeOf _ = mkNoRepType "GHC.ForeignPtr.ForeignPtr"
--   dataCast1 x  = gcast1 x
--
-- -- | @since base-4.11.0.0
-- deriving instance Data IntPtr
--
-- -- | @since base-4.11.0.0
-- deriving instance Data WordPtr
--
-- ------------------------------------------------------------------------------
-- -- The Data instance for Array preserves data abstraction at the cost of
-- -- inefficiency. We omit reflection services for the sake of data abstraction.
-- -- | @since base-4.8.0.0
-- instance (Data a, Data b, Ix a) => Data (Array a b)
--  where
--   gfoldl f z a = z (listArray (bounds a)) `f` (elems a)
--   toConstr _   = errorWithoutStackTrace "GHC.Internal.Data.Data.toConstr(Array)"
--   gunfold _ _  = errorWithoutStackTrace "GHC.Internal.Data.Data.gunfold(Array)"
--   dataTypeOf _ = mkNoRepType "Data.Array.Array"
--   dataCast2 x  = gcast2 x
--
-- ----------------------------------------------------------------------------
-- -- Data instance for Proxy
--
-- -- | @since base-4.7.0.0
-- deriving instance (Data t) => Data (Proxy t)
--
-- -- | @since base-4.7.0.0
-- deriving instance (a ~ b, Data a) => Data (a :~: b)
--
-- -- | @since base-4.10.0.0
-- deriving instance (Typeable i, Typeable j, Typeable a, Typeable b,
--                     (a :: i) ~~ (b :: j))
--     => Data (a :~~: b)
--
-- -- | @since base-4.7.0.0
-- deriving instance (Coercible a b, Data a, Data b) => Data (Coercion a b)
--
-- -- | @since base-4.9.0.0
-- deriving instance Data a => Data (Identity a)
--
-- -- | @since base-4.10.0.0
-- deriving instance (Typeable k, Data a, Typeable (b :: k)) => Data (Const a b)
--
-- -- | @since base-4.7.0.0
-- deriving instance Data Version
--
-- ----------------------------------------------------------------------------
-- -- Data instances for GHC.Internal.Data.Monoid wrappers
--
-- -- | @since base-4.8.0.0
-- deriving instance Data a => Data (Dual a)
--
-- -- | @since base-4.8.0.0
-- deriving instance Data All
--
-- -- | @since base-4.8.0.0
-- deriving instance Data Any
--
-- -- | @since base-4.8.0.0
-- deriving instance Data a => Data (Sum a)
--
-- -- | @since base-4.8.0.0
-- deriving instance Data a => Data (Product a)
--
-- -- | @since base-4.8.0.0
-- deriving instance Data a => Data (First a)
--
-- -- | @since base-4.8.0.0
-- deriving instance Data a => Data (Last a)
--
-- -- | @since base-4.8.0.0
-- deriving instance (Data (f a), Data a, Typeable f) => Data (Alt f a)
--
-- -- | @since base-4.12.0.0
-- deriving instance (Data (f a), Data a, Typeable f) => Data (Ap f a)
--
-- ----------------------------------------------------------------------------
-- -- Data instances for GHC.Generics representations
--
-- -- | @since base-4.9.0.0
-- deriving instance Data p => Data (U1 p)
--
-- -- | @since base-4.9.0.0
-- deriving instance Data p => Data (Par1 p)
--
-- -- | @since base-4.9.0.0
-- deriving instance (Data (f p), Typeable f, Data p) => Data (Rec1 f p)
--
-- -- | @since base-4.9.0.0
-- deriving instance (Typeable i, Data p, Data c) => Data (K1 i c p)
--
-- -- | @since base-4.9.0.0
-- deriving instance (Data p, Data (f p), Typeable c, Typeable i, Typeable f)
--     => Data (M1 i c f p)
--
-- -- | @since base-4.9.0.0
-- deriving instance (Typeable f, Typeable g, Data p, Data (f p), Data (g p))
--     => Data ((f :+: g) p)
--
-- -- | @since base-4.9.0.0
-- deriving instance (Typeable (f :: Type -> Type), Typeable (g :: Type -> Type),
--           Data p, Data (f (g p)))
--     => Data ((f :.: g) p)
--
-- -- | @since base-4.9.0.0
-- deriving instance Data p => Data (V1 p)
--
-- -- | @since base-4.9.0.0
-- deriving instance (Typeable f, Typeable g, Data p, Data (f p), Data (g p))
--     => Data ((f :*: g) p)
--
-- -- | @since base-4.9.0.0
-- deriving instance Data Generics.Fixity
--
-- -- | @since base-4.9.0.0
-- deriving instance Data Associativity
--
-- -- | @since base-4.9.0.0
-- deriving instance Data SourceUnpackedness
--
-- -- | @since base-4.9.0.0
-- deriving instance Data SourceStrictness
--
-- -- | @since base-4.9.0.0
-- deriving instance Data DecidedStrictness
--
-- ----------------------------------------------------------------------------
-- -- Data instances for GHC.Internal.Data.Ord
--
-- -- | @since base-4.12.0.0
-- deriving instance Data a => Data (Down a)
