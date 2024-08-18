module Engines.Transform where

import GHC.Plugins
    


class FullTransform a b where
  fullTransform :: Monad m => (a -> m a) -> b -> m b
  fullTransformTillFixedPoint :: (Monad m, Eq c) => (b -> c) -> (a -> m a) -> b -> m b
  fullTransformTillFixedPoint cmp f x
    = do x' <- fullTransform f x
         if cmp x == cmp x'
         then return x
         else fullTransformTillFixedPoint cmp f x'

instance FullTransform CoreExpr CoreExpr where
  fullTransform f (App a b)
    = do a' <- fullTransform f a
         b' <- fullTransform f b
         f $ App a' b'
  fullTransform f (Lam b e)
    = do e' <- fullTransform f e
         f $ Lam b e'
  fullTransform f (Let b e)
    = do e' <- fullTransform f e
         b' <- fullTransform f b
         f $ Let b' e'
  fullTransform f (Case e b t alts)
    = do e' <- fullTransform f e
         alts' <- fullTransform f alts
         f $ Case e' b t alts'
  fullTransform f (Cast e c)
    = do e' <- fullTransform f e
         f $ Cast e' c
  fullTransform f (Tick c e)
    = do e' <- fullTransform f e
         f $ Tick c e'
  fullTransform f x = f x

instance FullTransform a b => FullTransform a [b] where
  fullTransform f = mapM $ fullTransform f 

instance FullTransform CoreExpr CoreBind where
  fullTransform f (NonRec b e)
    = do e' <- fullTransform f e
         return $ NonRec b e'
  fullTransform f (Rec ls)
    = do ls' <- fullTransform f ls
         return $ Rec ls'

instance FullTransform CoreExpr (Id, CoreExpr) where
  fullTransform f (id', e)
    = do e' <- fullTransform f e
         return (id', e')

instance FullTransform CoreExpr (Alt Var) where
  fullTransform f (Alt alt_con bs e) 
    = do e' <- fullTransform f e
         return $ Alt alt_con bs e'

class Transform a c where
  transform :: forall b. (a -> Maybe b) -> (b -> CoreM a) -> c -> CoreM c

instance Transform CoreExpr CoreExpr where
  transform :: forall b. (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> CoreExpr -> CoreM CoreExpr
  transform checker transformation core_expr 
    | Just b <- checker core_expr = transformation b
  transform checker transformation (App f x) = do f' <- transform checker transformation f
                                                  x' <- transform checker transformation x
                                                  return $ App f' x'
  transform checker transformation (Lam b e) = do e' <- transform checker transformation e
                                                  return $ Lam b e'
  transform checker transformation (Let b e) = do
    b' <- transform checker transformation b
    e' <- transform checker transformation e
    return $ Let b' e'
  transform checker transformation (Case e b t alts) = do
    e' <- transform checker transformation e
    alts' <- mapM (transform checker transformation) alts
    return $ Case e' b t alts'
  transform checker transformation (Cast e c) = do 
    e' <- transform checker transformation e
    return $ Cast e' c
  transform checker transformation (Tick c e) = do
    e' <- transform checker transformation e
    return $ Tick c e'
  transform _ _ x = return x

instance Transform CoreExpr CoreBind where
  transform checker transformation (NonRec b e) = do e' <- transform checker transformation e
                                                     return $ NonRec b e'
  transform checker transformation (Rec ls) = Rec <$> mapM (transform checker transformation) ls

instance Transform CoreExpr (Id, CoreExpr) where
  transform :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> (Id, CoreExpr) -> CoreM (Id, CoreExpr)
  transform checker transformation (id', e) = do e' <- transform checker transformation e
                                                 return (id', e')

instance Transform CoreExpr (Alt Var) where
  transform :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> Alt Var -> CoreM (Alt Var)
  transform checker transformation (Alt alt_con bs e) = do e' <- transform checker transformation e
                                                           return $ Alt alt_con bs e'
