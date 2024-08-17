module Engines.KnownCase where
import GHC.Plugins
import Engines.LetInline (LetInlinable(letInline))
import Data.Maybe (fromMaybe)

class CaseOfKnownCase a where
  caseOfKnownCase :: a -> a

instance CaseOfKnownCase a => CaseOfKnownCase [a] where
  caseOfKnownCase :: CaseOfKnownCase a => [a] -> [a]
  caseOfKnownCase = map caseOfKnownCase

instance CaseOfKnownCase CoreExpr where
  caseOfKnownCase :: CoreExpr -> CoreExpr
  caseOfKnownCase (Case expr scrut t alts) = 
    fromMaybe (Case (caseOfKnownCase expr) scrut t (caseOfKnownCase alts)) $ do
      (datacon, _, term_arg) <- exprIsDataConAppMaybe expr
      (Alt _ vars rhs) <- getMatchingAltConMaybe datacon alts
      return $ letInline $ letBind vars term_arg rhs
    -- case exprIsDataConAppMaybe expr of 
    --   Just (datacon, _, term_arg) -> 
    --     case getMatchingAltConMaybe datacon alts of
    --       Just (Alt _ vars rhs) -> letInline $ letBind vars term_arg rhs
    --       Nothing -> Case (caseOfKnownCase expr) scrut t (caseOfKnownCase alts)
    --   Nothing -> Case (caseOfKnownCase expr) scrut t (caseOfKnownCase alts)
  caseOfKnownCase (App f x) = App (caseOfKnownCase f)
                                  (caseOfKnownCase x)
  caseOfKnownCase (Lam b e) = Lam b (caseOfKnownCase e)
  caseOfKnownCase (Let b e) = Let (caseOfKnownCase b)
                                  (caseOfKnownCase e)
  caseOfKnownCase (Cast e c) = Cast (caseOfKnownCase e)
                                    c
  caseOfKnownCase (Tick c e) = Tick c (caseOfKnownCase e)
  caseOfKnownCase e = e

instance CaseOfKnownCase (Alt Var) where
  caseOfKnownCase :: Alt Var -> Alt Var
  caseOfKnownCase (Alt alt_con b e) = Alt alt_con b (caseOfKnownCase e)

instance CaseOfKnownCase CoreBind where
  caseOfKnownCase :: CoreBind -> CoreBind
  caseOfKnownCase (NonRec b e) = NonRec b (caseOfKnownCase e)
  caseOfKnownCase (Rec ls) = Rec $ caseOfKnownCase ls

instance CaseOfKnownCase (Id, CoreExpr) where
  caseOfKnownCase :: (Id, CoreExpr) -> (Id, CoreExpr)
  caseOfKnownCase (id', e) = (id', caseOfKnownCase e)

exprIsDataConAppMaybe :: CoreExpr -> Maybe (DataCon, [Type], [CoreExpr])
exprIsDataConAppMaybe (App (Var id') (Type t)) = (, [t], []) <$> isDataConId_maybe id'
exprIsDataConAppMaybe (App (Var id') e) = (, [], [e]) <$> isDataConId_maybe id'
exprIsDataConAppMaybe (App f (Type e)) 
  | Just (dc, ty_args, t_args) <- exprIsDataConAppMaybe f
    = Just (dc, ty_args ++ [e], t_args)
exprIsDataConAppMaybe (App f e) 
  | Just (dc, ty_args, t_args) <- exprIsDataConAppMaybe f
    = Just (dc, ty_args, t_args ++ [e])
exprIsDataConAppMaybe _ = Nothing

getMatchingAltConMaybe :: DataCon -> [Alt Var] -> Maybe (Alt Var)
getMatchingAltConMaybe _ [] = Nothing
getMatchingAltConMaybe _ (Alt DEFAULT _ _ : _)  = Nothing
getMatchingAltConMaybe dc (a@(Alt (DataAlt da) _ _) : _)
  | dc == da = Just a
getMatchingAltConMaybe dc (_ : xs) = getMatchingAltConMaybe dc xs

letBind :: [Id] -> [CoreExpr] -> CoreExpr -> CoreExpr
letBind [] [] rhs = rhs
letBind (v : vs) (b : bs) rhs = Let (NonRec v b) (letBind vs bs rhs) 
letBind _ _ _ = panic "Mismatch of let-bound variables and expressions"
