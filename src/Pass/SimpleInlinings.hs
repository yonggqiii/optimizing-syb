module Pass.SimpleInlinings(simpleInlinings) where

import GHC.Plugins
import Utils hiding (prt)
import Engines.LetInline (LetInlinable(letInline))
import Engines.Transform
import GHC.Core.Map.Type (deBruijnize)
import Control.Monad
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
simpleInlinings :: Opts -> CoreToDo
simpleInlinings opts = CoreDoPluginPass "Simple Inlinings" (simpleInlineModGuts opts)

prt :: Outputable a => Opts -> a -> CoreM ()
prt opts = prtIf (show_simple opts)
prtS :: Opts -> String -> CoreM ()
prtS opts = putMsgSIf (show_simple opts)


simpleInlineModGuts :: Opts ->  CorePluginPass
simpleInlineModGuts opts mod_guts = do
  prtS opts $ info "Running simple inlinings phase"
  let all_binds :: [CoreBind] = mg_binds mod_guts
  new_binds <- mapM (inlineCoreBind opts) all_binds
  let new_mod_guts = mod_guts { mg_binds = new_binds }
  return new_mod_guts

inlineCoreBind :: Opts -> CoreBind -> CoreM CoreBind
inlineCoreBind opts (NonRec b e) = do
  e'' <- fullTransformM (inlineCoreExpr opts) e
  let e' = letInline e''
  when (deBruijnize e' /= deBruijnize e'')
    $ do prtS opts (info "Target expression found")
         prt opts e''
         prtS opts (success "New expression")
         prt opts e'
  return $ NonRec b e'
inlineCoreBind opts (Rec ls) = do
    ls' <- aux ls
    return $ Rec ls'
  where aux :: [(Var, Expr Var)] -> CoreM [(Var, Expr Var)]
        aux [] = return []
        aux ((b, e) : xs) = do
          xs' <- aux xs
          e'' <- fullTransformM (inlineCoreExpr opts) e
          let e' = letInline e''
          when (deBruijnize e' /= deBruijnize e'')
            $ do prtS opts (info "Target expression found")
                 prt opts e''
                 prtS opts (success "New expression")
                 prt opts e'
          return $ (b, e') : xs'

inlineCoreExpr :: Opts -> Expr Var -> CoreM (Expr Var)
inlineCoreExpr opts e@(App (App (App (App (App (Var dollar) (Type _)) (Type _)) (Type _)) f) x)
  | nameStableString (varName dollar) == "$base$GHC.Base$$" = do
      prtS opts $ info "Target expression found"
      prt opts e
      let res = App f x
      prtS opts $ success "New expression"
      prt opts res
      return res
inlineCoreExpr _ x = return x

