module Engines.LetInline where

import GHC.Plugins
import Engines.Substitution
class LetInlinable a where
  letInline :: a -> a

instance LetInlinable a => LetInlinable [a] where
  letInline = map letInline

instance LetInlinable CoreExpr where
  letInline (Let b e) =
    let b' = letInline b
        e' = letInline e
    in  case b' of 
          NonRec lhs rhs -> substitute lhs rhs e'
          -- do not let-inline recursive binds
          Rec _ -> Let b' e'
  letInline (App f x) = App (letInline f) (letInline x)
  letInline (Lam b e) = Lam b (letInline e)
  letInline (Case e v t alts) = Case (letInline e) v t (letInline alts)
  letInline (Cast e c) = Cast (letInline e) c
  letInline (Tick c e) = Tick c (letInline e)
  letInline x = x

instance LetInlinable CoreBind where
  letInline (NonRec lhs rhs) = NonRec lhs (letInline rhs)
  letInline (Rec ls) = Rec (letInline ls)

instance LetInlinable (Id, CoreExpr) where
  letInline (lhs, rhs) = (lhs, letInline rhs)

instance LetInlinable (Alt Var) where
  letInline (Alt alt_con v e) = Alt alt_con v (letInline e)
