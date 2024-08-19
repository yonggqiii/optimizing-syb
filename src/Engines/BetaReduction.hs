module Engines.BetaReduction where

import Engines.Substitution(substitute)
import GHC.Plugins
import GHC.IO (unsafePerformIO)
import Engines.Transform
import GHC.Core.Map.Type

betaReducerM :: CoreExpr -> CoreM CoreExpr
betaReducerM (App (Lam var rhs) x) = return $ substitute var x rhs
betaReducerM (App (Cast (Lam var rhs) c) (Type x)) = do
  -- putMsgS "BR on COERCION"
  -- putMsg $ ppr (App (Cast (Lam var rhs) c) (Type x))
  -- putMsgS "COERCION"
  -- putMsg $ ppr  c
  -- putMsgS "COERCION TYPE"
  -- putMsg $ ppr  $ coercionType c
  -- putMsgS "COERCION KIND"
  -- putMsg $ ppr $ coercionKind c
  -- putMsgS "splitForAllCo_maybe"
  let Just (tv, e, f) = splitForAllCo_ty_maybe c
  -- putMsgS "TYVAR"
  -- putMsg $ ppr tv
  -- putMsgS "e COERCION"
  -- putMsg $ ppr e
  -- putMsgS "e COERCION TYPE"
  -- putMsg $ ppr $ coercionType e
  -- putMsgS "e COERCION KIND"
  -- putMsg $ ppr $ coercionKind e
  --
  -- putMsgS "f coercion"
  -- putMsg $ ppr f
  -- putMsgS "f COERCION TYPE"
  -- putMsg $ ppr $ coercionType f
  -- putMsgS "f COERCION KIND"
  -- putMsg $ ppr $ coercionKind f
  let newFCoercion = substitute tv x f
  -- putMsgS "SUBSTITUTED COERCION"
  -- putMsg $ ppr $ newFCoercion
  -- putMsgS " ============================== "
  let newTerm = substitute var x rhs
  -- putMsgS "NEW TERM"
  -- putMsg $ ppr $ newTerm
  -- putMsgS " ============================== "
  -- putMsgS "NEW CAST"
  let newCast = Cast newTerm newFCoercion
  -- putMsg $ ppr $ newCast
  return newCast
betaReducerM (App (Cast (Lam var rhs) c) x) = do
  putMsgS "BR on COERCION"
  putMsg $ ppr (App (Cast (Lam var rhs) c) x)
  putMsgS "COERCION"
  putMsg $ ppr  c
  putMsgS "COERCION TYPE"
  putMsg $ ppr  $ coercionType c
  putMsgS "COERCION KIND"
  putMsg $ ppr $ coercionKind c
  putMsgS "SPLIT FUNCO"
  let Just (e, f) = splitFunCo_maybe c
  putMsgS "E COERCION"
  putMsg $ ppr $ e
  putMsgS "F COERCION"
  putMsg $ ppr $ f
  let newTerm = substitute var x rhs
  return $ Cast newTerm f
  -- return $ App (Cast (Lam var rhs) c) x
betaReducerM x = return x

betaReduceM :: (FullTransform CoreExpr a) => a -> CoreM a
betaReduceM = fullTransformM betaReducerM

betaReduceCompletelyM :: (Eq (DeBruijn a), FullTransform CoreExpr a) => a -> CoreM a
betaReduceCompletelyM = fullTransformMTillFixedPoint deBruijnize betaReducerM

betaReducer :: CoreExpr -> CoreExpr
betaReducer (App (Lam var rhs) x) = substitute var x rhs
betaReducer x = x 

betaReduce :: (FullTransform CoreExpr a) => a -> a
betaReduce = fullTransform betaReducer

betaReduceCompletely :: (Eq (DeBruijn a), FullTransform CoreExpr a) => a -> a
betaReduceCompletely = fullTransformTillFixedPoint deBruijnize betaReducer

-- betaReduceCompletely :: (BetaReducible a, Eq b) => a -> (a -> b) -> a
-- betaReduceCompletely e eq
--     | eq e == eq e' = e
--     | otherwise     = betaReduceCompletely e' eq
--   where e' = betaReduce e
--                                             

-- class BetaReducible a where
--   betaReduce :: a -> a
--
-- instance BetaReducible a => BetaReducible [a] where
--   betaReduce :: BetaReducible a => [a] -> [a]
--   betaReduce = map betaReduce
--
-- instance BetaReducible CoreExpr where
--   betaReduce :: CoreExpr -> CoreExpr
--   betaReduce e@(Var _) = e
--   betaReduce e@(Lit _) = e
--   betaReduce (App f x) = 
--     let f' = betaReduce f
--         x' = betaReduce x
--     in  case f' of 
--           (Lam var rhs) -> substitute var x' rhs
--           e -> App e x'
--   -- betaReduce (App f x) = 
--   --   let f' = betaReduce f
--   --       x' = betaReduce x
--   --   in  case f' of 
--   --         (Lam var rhs) -> case x' of 
--   --           -- (Type t) -> let iss = emptyInScopeSet
--   --           --                 tvEnv = unitVarEnv var t
--   --           --                 idEnv = emptyVarEnv
--   --           --                 cvEnv = emptyVarEnv
--   --           --                 s = Subst iss idEnv tvEnv cvEnv
--   --           --             in seq (unsafePerformIO (putStrLn (showSDocUnsafe (ppr f')))) $ 
--   --           --                 seq (unsafePerformIO (putStrLn (showSDocUnsafe (ppr x')))) $ 
--   --           --                   substExpr s rhs-- do the substitution
--   --           e -> let iss = emptyInScopeSet
--   --                    tvEnv = emptyVarEnv 
--   --                    idEnv = unitVarEnv var e
--   --                    cvEnv = emptyVarEnv
--   --                    s = Subst iss idEnv tvEnv cvEnv
--   --                in substExpr s rhs-- do the substitution
--   --
--   --         e -> App e x'
--   betaReduce (Lam b e) = Lam b (betaReduce e)
--   betaReduce (Let b e) = Let (betaReduce b) (betaReduce e)
--   betaReduce (Case e v t alts) = Case (betaReduce e)
--                                       v
--                                       t
--                                       (betaReduce alts)
--   betaReduce (Cast e c) = Cast (betaReduce e) c
--   betaReduce (Tick c e) = Tick c (betaReduce e)
--   betaReduce t@(Type _) = t
--   betaReduce c@(Coercion _) = c
--
-- instance BetaReducible CoreBind where
--   betaReduce (NonRec lhs rhs) = NonRec lhs (betaReduce rhs)
--   betaReduce (Rec ls) = Rec $ betaReduce ls
--
-- instance BetaReducible (Id, CoreExpr) where
--   betaReduce (lhs, rhs) = (lhs, betaReduce rhs)
--
-- instance BetaReducible (Alt Var) where
--   betaReduce (Alt alt_con t e) = Alt alt_con t (betaReduce e)
--
--
