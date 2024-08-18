module Engines.InlineUnfolding where
import GHC.Plugins

inlineId :: Id -> CoreM CoreExpr
inlineId v = do
  let uf = realIdUnfolding v
  case uf of 
    DFunUnfolding bndrs df_con df_args -> do
      -- --prt%%%bndrs
      -- --prt%%%df_con
      -- --prt%%%$ dataConRepType df_con
      -- --prt%%%df_args
      let dfune = mkCoreConApps df_con df_args
      let dfun = foldr Lam dfune bndrs
      --putMsgS%%%"=== GENERATED DFUN ==="
      --prt%%% dfun
      return  dfun
    CoreUnfolding tmpl _ _ _ _ -> do
      return tmpl
    OtherCon s -> do
      --putMsgS%%%"=== OTHERCON ==="
      --prt%%%v
      return $ Var v
    NoUnfolding -> do
      --putMsgS%%%"=== NO UNFOLDING ==="
      --prt%%%v
      return $ Var v

    _ -> do
      --putMsgS%%%"=== NO UNFOLDING!? ==="
      --prt%%%v
      return $ Var v
