module Pass.SimpleInlinings(simpleInlinings) where

import GHC.Plugins
import Engines.LetInline (LetInlinable(letInline))

{- This phase genuinely exists only to expose the interesting structure that 
 - we want to specialize. 
 -
 - Currently, we have only implemented the case of 
 -      everywhere $ f 
 - for example. 
 -
 - Later on, we might replace this phase with the simple optimizer, or add more 
 - cases as necessary. -}

-- | 'simpleInlinings' is a very simple plugin that performs simple inlinings on a freshly 
-- desugared program. Currently, it only inlines any fully-applied occurrences of '($)'
simpleInlinings :: CoreToDo
simpleInlinings = CoreDoPluginPass "Simple Inlinings" simpleInlineModGuts

simpleInlineModGuts :: CorePluginPass
simpleInlineModGuts mod_guts = do
  putMsgS "=== Simple Inlinings ==="
  let all_binds :: [CoreBind] = mg_binds mod_guts
  new_binds <- mapM inlineCoreBind all_binds
  let new_mod_guts = mod_guts { mg_binds = new_binds }
  return new_mod_guts

inlineCoreBind :: CoreBind -> CoreM CoreBind
inlineCoreBind (NonRec b e) = do
  e' <- inlineCoreExpr $ letInline e
  return $ NonRec b e'
inlineCoreBind (Rec ls) = do
    ls' <- aux ls
    return $ Rec ls'
  where aux :: [(Var, Expr Var)] -> CoreM [(Var, Expr Var)]
        aux [] = return []
        aux ((b, e) : xs) = do
          xs' <- aux xs
          e'  <- inlineCoreExpr $ letInline e
          return $ (b, e') : xs'

inlineCoreExpr :: Expr Var -> CoreM (Expr Var)
inlineCoreExpr e@(App (App (App (App (App (Var dollar) (Type _)) (Type _)) (Type _)) f) x)
  | nameStableString (varName dollar) == "$base$GHC.Base$$" = do
      putMsgS "Expr found"
      putMsg $ ppr e
      f' <- inlineCoreExpr f
      x' <- inlineCoreExpr x
      let res = App f' x'
      putMsgS "New expr"
      putMsg $ ppr res
      return res
inlineCoreExpr (Var f) = return $ Var f
inlineCoreExpr (Lit x) = return $ Lit x
inlineCoreExpr (App f x) = do
  f' <- inlineCoreExpr f
  x' <- inlineCoreExpr x
  return $ App f' x'
inlineCoreExpr (Lam b e) = do
  e' <- inlineCoreExpr e
  return $ Lam b e'
inlineCoreExpr (Let bind e) = do
  bind' <- inlineCoreBind bind
  e'    <- inlineCoreExpr e
  return $ Let bind' e'
inlineCoreExpr (Case e b t alts) = do
    e' <- inlineCoreExpr e
    alts' <- aux alts
    return $ Case e' b t alts'
  where aux :: [Alt Var] -> CoreM [Alt Var]
        aux [] = return []
        aux (Alt alt_con ls_b expr : xs) = do
          xs' <- aux xs
          e'  <- inlineCoreExpr expr
          return $ Alt alt_con ls_b e' : xs'
inlineCoreExpr (Cast e r) = do 
  e' <- inlineCoreExpr e
  return $ Cast e' r
inlineCoreExpr (Tick c e) = do
  e' <- inlineCoreExpr e
  return $ Tick c e'
inlineCoreExpr (Type t) = return (Type t)
inlineCoreExpr (Coercion c) = return $ Coercion c
