module Engines.InlineUnfolding where
import GHC.Plugins
import Data.Maybe

-- | Produces the unfolding of an 'Id'
inlineId :: Id -> Maybe CoreExpr
inlineId = maybeUnfoldingTemplate . realIdUnfolding

class InlineUnfolding a where
  inlineUnfolding :: Id -> a -> a

instance InlineUnfolding CoreExpr where
  inlineUnfolding :: Id -> CoreExpr -> CoreExpr
  inlineUnfolding id' e@(Var var)
    | id' == var = fromMaybe e (inlineId id')
    | otherwise  = e
  inlineUnfolding _ e@(Lit _) = e
  inlineUnfolding id' (App f x) = App (inlineUnfolding id' f) (inlineUnfolding id' x)
  inlineUnfolding id' (Lam b e) = Lam b (inlineUnfolding id' e)
  inlineUnfolding id' (Let bind e) = Let (inlineUnfolding id' bind) (inlineUnfolding id' e)
  inlineUnfolding id' (Case e v t alts) = Case (inlineUnfolding id' e) v t (inlineUnfolding id' alts)
  inlineUnfolding id' (Cast e c) = Cast (inlineUnfolding id' e) c
  inlineUnfolding id' (Tick c e) = Tick c $ inlineUnfolding id' e
  inlineUnfolding _ (Type t) = Type t
  inlineUnfolding _ (Coercion c) = Coercion c

instance InlineUnfolding a => InlineUnfolding [a] where
  inlineUnfolding :: InlineUnfolding a => Id -> [a] -> [a]
  inlineUnfolding id' = map (inlineUnfolding id')


instance InlineUnfolding CoreBind where
  inlineUnfolding :: Id -> CoreBind -> CoreBind
  inlineUnfolding id' (NonRec b e ) = NonRec b (inlineUnfolding id' e)
  inlineUnfolding id' (Rec ls) = Rec $ inlineUnfolding id' ls

instance InlineUnfolding (Id, CoreExpr) where
  inlineUnfolding :: Id -> (Id, CoreExpr) -> (Id, CoreExpr)
  inlineUnfolding id' (id'', e) = (id'', inlineUnfolding id' e)

instance InlineUnfolding (Alt Var) where
  inlineUnfolding :: Id -> Alt Var -> Alt Var
  inlineUnfolding id' (Alt alt_con bs e) = Alt alt_con bs (inlineUnfolding id' e)
