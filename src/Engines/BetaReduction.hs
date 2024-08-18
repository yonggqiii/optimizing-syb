module Engines.BetaReduction where

import Engines.Substitution(substitute)
import GHC.Plugins
import GHC.IO (unsafePerformIO)
import Engines.Transform
import GHC.Core.Map.Type

betaReducer :: Monad m => CoreExpr -> m CoreExpr
betaReducer (App (Lam var rhs) x) = return $ substitute var x rhs
betaReducer x = return x

betaReduce' :: (FullTransform CoreExpr a, Monad m) => a -> m a
betaReduce' = fullTransform betaReducer

betaReduceCompletely' :: (Eq (DeBruijn a), FullTransform CoreExpr a, Monad m) => a -> m a
betaReduceCompletely' = fullTransformTillFixedPoint deBruijnize betaReducer

betaReduceCompletely :: (BetaReducible a, Eq b) => a -> (a -> b) -> a
betaReduceCompletely e eq
    | eq e == eq e' = e
    | otherwise     = betaReduceCompletely e' eq
  where e' = betaReduce e
                                            

class BetaReducible a where
  betaReduce :: a -> a

instance BetaReducible a => BetaReducible [a] where
  betaReduce :: BetaReducible a => [a] -> [a]
  betaReduce = map betaReduce

instance BetaReducible CoreExpr where
  betaReduce :: CoreExpr -> CoreExpr
  betaReduce e@(Var _) = e
  betaReduce e@(Lit _) = e
  betaReduce (App f x) = 
    let f' = betaReduce f
        x' = betaReduce x
    in  case f' of 
          (Lam var rhs) -> substitute var x' rhs
          e -> App e x'
  -- betaReduce (App f x) = 
  --   let f' = betaReduce f
  --       x' = betaReduce x
  --   in  case f' of 
  --         (Lam var rhs) -> case x' of 
  --           -- (Type t) -> let iss = emptyInScopeSet
  --           --                 tvEnv = unitVarEnv var t
  --           --                 idEnv = emptyVarEnv
  --           --                 cvEnv = emptyVarEnv
  --           --                 s = Subst iss idEnv tvEnv cvEnv
  --           --             in seq (unsafePerformIO (putStrLn (showSDocUnsafe (ppr f')))) $ 
  --           --                 seq (unsafePerformIO (putStrLn (showSDocUnsafe (ppr x')))) $ 
  --           --                   substExpr s rhs-- do the substitution
  --           e -> let iss = emptyInScopeSet
  --                    tvEnv = emptyVarEnv 
  --                    idEnv = unitVarEnv var e
  --                    cvEnv = emptyVarEnv
  --                    s = Subst iss idEnv tvEnv cvEnv
  --                in substExpr s rhs-- do the substitution
  --
  --         e -> App e x'
  betaReduce (Lam b e) = Lam b (betaReduce e)
  betaReduce (Let b e) = Let (betaReduce b) (betaReduce e)
  betaReduce (Case e v t alts) = Case (betaReduce e)
                                      v
                                      t
                                      (betaReduce alts)
  betaReduce (Cast e c) = Cast (betaReduce e) c
  betaReduce (Tick c e) = Tick c (betaReduce e)
  betaReduce t@(Type _) = t
  betaReduce c@(Coercion _) = c

instance BetaReducible CoreBind where
  betaReduce (NonRec lhs rhs) = NonRec lhs (betaReduce rhs)
  betaReduce (Rec ls) = Rec $ betaReduce ls

instance BetaReducible (Id, CoreExpr) where
  betaReduce (lhs, rhs) = (lhs, betaReduce rhs)

instance BetaReducible (Alt Var) where
  betaReduce (Alt alt_con t e) = Alt alt_con t (betaReduce e)


