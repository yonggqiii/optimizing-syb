module Engines.Transform where

import GHC.Plugins

class FullTransform a b where
  fullTransform :: (a -> a) -> b -> b
  fullTransformM :: Monad m => (a -> m a) -> b -> m b
  fullTransformMTillFixedPoint :: (Monad m, Eq c) => (b -> c) -> (a -> m a) -> b -> m b
  fullTransformMTillFixedPoint cmp f x
    = do x' <- fullTransformM f x
         if cmp x == cmp x'
         then return x
         else fullTransformMTillFixedPoint cmp f x'
  fullTransformTillFixedPoint :: Eq c => (b -> c) -> (a -> a) -> b -> b
  fullTransformTillFixedPoint cmp f x
    = let x' = fullTransform f x
      in  if cmp x == cmp x'
          then x
          else fullTransformTillFixedPoint cmp f x'

instance FullTransform CoreExpr CoreExpr where
  fullTransform f (App a b) 
    = let a' = fullTransform f a
          b' = fullTransform f b
      in  f $ App a' b'
  fullTransform f (Lam b e)
    = let e' = fullTransform f e
      in  f $ Lam b e'
  fullTransform f (Case e b t alts) 
    = let e' = f e
          alts' = fullTransform f alts
      in  f $ Case e' b t alts'
  fullTransform f (Cast e c)
    = let e' = fullTransform f e
      in  f $ Cast e' c
  fullTransform f (Tick c e)
    = let e' = fullTransform f e
      in  f $ Tick c e'
  fullTransform f x = f x
  fullTransformM f (App a b)
    = do a' <- fullTransformM f a
         b' <- fullTransformM f b
         f $ App a' b'
  fullTransformM f (Lam b e)
    = do e' <- fullTransformM f e
         f $ Lam b e'
  fullTransformM f (Let b e)
    = do e' <- fullTransformM f e
         b' <- fullTransformM f b
         f $ Let b' e'
  fullTransformM f (Case e b t alts)
    = do e' <- fullTransformM f e
         alts' <- fullTransformM f alts
         f $ Case e' b t alts'
  fullTransformM f (Cast e c)
    = do e' <- fullTransformM f e
         f $ Cast e' c
  fullTransformM f (Tick c e)
    = do e' <- fullTransformM f e
         f $ Tick c e'
  fullTransformM f x = f x

instance FullTransform a b => FullTransform a [b] where
  fullTransform f = map $ fullTransform f
  fullTransformM :: (FullTransform a b, Monad m) => (a -> m a) -> [b] -> m [b]
  fullTransformM f = mapM $ fullTransformM f 

instance FullTransform CoreExpr CoreBind where
  fullTransform f (NonRec b e)
    = let e' = fullTransform f e
      in  NonRec b e'
  fullTransform f (Rec ls) = Rec $ fullTransform f ls
  fullTransformM f (NonRec b e)
    = do e' <- fullTransformM f e
         return $ NonRec b e'
  fullTransformM f (Rec ls)
    = do ls' <- fullTransformM f ls
         return $ Rec ls'

instance FullTransform CoreExpr (Id, CoreExpr) where
  fullTransform f (id', e) = (id', fullTransform f e)
  fullTransformM f (id', e)
    = do e' <- fullTransformM f e
         return (id', e')

instance FullTransform CoreExpr (Alt Var) where
  fullTransform f (Alt alt_con bs e) = Alt alt_con bs $ fullTransform f e
  fullTransformM f (Alt alt_con bs e) 
    = do e' <- fullTransformM f e
         return $ Alt alt_con bs e'

