module Engines.Transform where

import GHC.Plugins

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
