module Engines.DropCasts where

import GHC.Plugins
{- Highly risky operation. Know what you are doing! -}
class DropCasts a where
  dropCasts :: a -> a

instance DropCasts a => DropCasts [a] where
  dropCasts :: DropCasts a => [a] -> [a]
  dropCasts = map dropCasts
instance DropCasts CoreExpr where
  dropCasts :: CoreExpr -> CoreExpr
  dropCasts (Cast e c) = dropCasts e
  dropCasts (App f x) = App (dropCasts f) (dropCasts x)
  dropCasts (Lam b e) = Lam b (dropCasts e)
  dropCasts (Let b e) = Let (dropCasts b) (dropCasts e)
  dropCasts (Case e b t a) = Case (dropCasts e) b t (dropCasts a)
  dropCasts (Tick c e) = Tick c (dropCasts e)
  dropCasts x = x

instance DropCasts (Alt Var) where
  dropCasts :: Alt Var -> Alt Var
  dropCasts (Alt alt_con v e) = Alt alt_con v (dropCasts e)
instance DropCasts CoreBind where
  dropCasts :: CoreBind -> CoreBind
  dropCasts (NonRec b e) = NonRec b (dropCasts e)
  dropCasts (Rec ls) = Rec $ dropCasts ls

instance DropCasts (Id, CoreExpr) where
  dropCasts :: (Id, CoreExpr) -> (Id, CoreExpr)
  dropCasts (i, e) = (i, dropCasts e)
