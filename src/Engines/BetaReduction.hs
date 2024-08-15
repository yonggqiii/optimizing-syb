module Engines.BetaReduction where

import Engines.Substitution(substitute)
import GHC.Plugins

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
