module Engines.InlineUnfolding where
import GHC.Plugins

inlineId :: Id -> CoreM CoreExpr
inlineId v = do
  let uf = realIdUnfolding v
  case uf of 
    DFunUnfolding bndrs df_con df_args -> do
      let dfune = mkCoreConApps df_con df_args
      let dfun = foldr Lam dfune bndrs
      return  dfun
    CoreUnfolding tmpl _ _ _ _ -> do
      return tmpl
    OtherCon _ -> do
      return $ Var v
    NoUnfolding -> do
      return $ Var v
    _ -> do
      return $ Var v
