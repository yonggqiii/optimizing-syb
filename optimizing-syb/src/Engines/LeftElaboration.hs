module Engines.LeftElaboration where

import GHC.Core.Map.Type (deBruijnize)
import GHC.Plugins

leftElaborationLikeCrazy :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> CoreExpr -> CoreM CoreExpr
leftElaborationLikeCrazy extractor elaboration expr =
  do
    e' <- leftElaboration extractor elaboration expr
    if deBruijnize expr == deBruijnize e'
      then return expr
      else leftElaborationLikeCrazy extractor elaboration e'

leftElaboration :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> CoreExpr -> CoreM CoreExpr
leftElaboration extractor elaboration expr
  | Just b <- extractor expr =
      elaboration b
leftElaboration extractor elaboration (Lam b e) = do
  e' <- leftElaboration extractor elaboration e
  return $ Lam b e'
leftElaboration extractor elaboration (App f x) = do
  f' <- leftElaboration extractor elaboration f
  return $ App f' x
leftElaboration extractor elaboration (Cast e c) = do
  e' <- leftElaboration extractor elaboration e
  return $ Cast e' c
leftElaboration extractor elaboration (Case e b t alts) = do
  alts' <- mapM (leftElaborationAlts extractor elaboration) alts
  return $ Case e b t alts'
leftElaboration _ _ x = return x

leftElaborationAlts :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> Alt CoreBndr -> CoreM (Alt CoreBndr)
leftElaborationAlts extractor elaboration (Alt alt_con b e) =
  do
    e' <- leftElaboration extractor elaboration e
    return $ Alt alt_con b e'
