module Engines.LeftElaboration where

import GHC.Plugins 
import GHC.Core.Map.Type (deBruijnize)

leftElaborationLikeCrazy :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> (CoreExpr -> CoreExpr) -> CoreExpr -> CoreM CoreExpr
leftElaborationLikeCrazy extractor elaboration post_processor expr 
  = do --putMsgS "LEFT ELAB"
       --putMsg $ ppr expr
       e' <- leftElaboration extractor elaboration id expr --post_processor expr
       --putMsgS "HERE"
       --putMsg $ ppr e'
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
leftElaboration extractor elaboration post_process (Cast e c) = do e' <- leftElaboration extractor elaboration post_process e
                                                                   return $ post_process $ Cast e' c
leftElaboration extractor elaboration post_process (Case e b t alts) = do alts' <- mapM (leftElaborationAlts extractor elaboration post_process) alts
                                                                          return $ Case e b t alts'
leftElaboration _ _ post_process x = return $ post_process x


leftElaborationAlts :: (CoreExpr -> Maybe b) -> (b -> CoreM CoreExpr) -> (CoreExpr -> CoreExpr) -> Alt CoreBndr -> CoreM (Alt CoreBndr)
leftElaborationAlts extractor elaboration post_process (Alt alt_con b e) 
  = do e' <- leftElaboration extractor elaboration post_process e
       return $ Alt alt_con b e'
