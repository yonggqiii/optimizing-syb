module Engines.LeftElaboration where

import GHC.Plugins 
import GHC.Core.Map.Type (deBruijnize)

leftElaborationLikeCrazy :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> (CoreExpr -> CoreExpr) -> CoreExpr -> CoreM CoreExpr
leftElaborationLikeCrazy extractor elaboration post_processor expr 
  = do e' <- leftElaboration extractor elaboration post_processor expr
       if deBruijnize expr == deBruijnize e'
       then return expr
       else leftElaborationLikeCrazy extractor elaboration post_processor e'

leftElaboration :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> (CoreExpr -> CoreExpr) -> CoreExpr -> CoreM CoreExpr
leftElaboration extractor elaboration post_process expr
  | Just b <- extractor expr
    = post_process <$> elaboration b
leftElaboration extractor elaboration post_process (Lam b e) = do e' <- leftElaboration extractor elaboration post_process e
                                                                  return $ post_process $ Lam b e'
leftElaboration extractor elaboration post_process (App f x) = do f' <- leftElaboration extractor elaboration post_process f
                                                                  return $ post_process $ App f' x
leftElaboration _ _ post_process x = return $ post_process x
