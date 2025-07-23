{-# LANGUAGE LambdaCase #-}

module Engines.BetaReduction where

import Engines.Transform
import GHC.Core.Map.Type
import GHC.Data.Pair
import GHC.Plugins

getFVs :: CoreExpr -> InScopeSet
getFVs e = extendInScopeSetList emptyInScopeSet (exprFreeVarsList e)

performSubstitution' :: Var -> CoreExpr -> CoreExpr -> CoreExpr
performSubstitution' var (Coercion c) expr
  | isCoVar var =
      let iss = getFVs expr
          subst = Subst iss emptyVarEnv emptyVarEnv (unitVarEnv var c)
          new_expr = substExpr subst expr
       in new_expr
  | otherwise = panic "Substitution on coercion argument but not on coercion variable!"
performSubstitution' var (Type t) expr
  | isTyVar var =
      let iss = getFVs expr
          subst = Subst iss emptyVarEnv (unitVarEnv var t) emptyVarEnv
          new_expr = substExpr subst expr
       in new_expr
  | otherwise = panic "Substitution on type argument but not on type variable!"
performSubstitution' var e expr
  | isId var =
      let iss = getFVs expr
          subst = Subst iss (unitVarEnv var e) emptyVarEnv emptyVarEnv
          new_expr = substExpr subst expr
       in new_expr
  | otherwise = panic "Substitution on term argument but not on term variable!"

betaReducerM :: CoreExpr -> CoreM CoreExpr
-- Test out some cast simplifications
betaReducerM expr@(Cast e c)
  | isReflexiveCo c = do
      -- putMsgS "Performing Beta Reduction on cast to reflexive coercion. Before:"
      -- putMsg $ ppr expr
      -- putMsgS "After:"
      -- putMsg $ ppr e
      return e
betaReducerM expr@(Cast (Cast e c_1) c_2) = do
  -- putMsgS "Performing Beta Reduction on double cast. Before:"
  -- putMsg $ ppr expr
  -- putMsgS "After:"
  let new_expr = Cast e (mkTransCo c_1 c_2)
  -- putMsg $ ppr new_expr
  return new_expr
betaReducerM expr@(Cast (Let b e) c) = do
  -- putMsgS "Performing let-float on cast. Before:"
  -- putMsg $ ppr expr
  -- putMsgS "After:"
  let new_expr = Let b (Cast e c)
  -- putMsg $ ppr new_expr
  return new_expr
betaReducerM expr@(Cast (Case e b t alts) c) = do
  let Pair l r = coercionKind c
  -- putMsgS "Performing cast insertion into cases."
  -- putMsgS "Left"
  -- putMsg $ ppr l
  -- putMsgS "Right"
  -- putMsg $ ppr r
  -- putMsgS "Type"
  -- putMsg $ ppr t
  -- putMsgS "BEfore"
  -- putMsg $ ppr expr
  let new_alts = (\case (Alt ac b' e') -> Alt ac b' (Cast e' c)) <$> alts
  let new_expr = Case e b r new_alts
  -- putMsgS "After:"
  -- putMsg $ ppr new_expr
  return new_expr
betaReducerM expr@(App (Lam var rhs) x) = do
  -- putMsgS "Performing BETA REDUCTION on var. BEFORE:"
  -- putMsg $ ppr expr
  -- putMsgS "AFTER:"
  let new_expr = performSubstitution' var x rhs
  -- putMsg $ ppr new_expr
  return new_expr
betaReducerM expr@(Case e _ _ alts)
  | Just (datacon, _, term_arg) <- exprIsDataConAppMaybe e,
    Just (Alt (DataAlt _) vars rhs) <- getMatchingAltConMaybe datacon alts =
      do
        -- putMsgS "Performing BETA REDUCTION of case of known constructor. BEFORE:"
        -- putMsg $ ppr expr
        let new_expr = performSubstitutionList vars term_arg rhs
        -- putMsgS "AFTER:"
        -- putMsg $ ppr new_expr
        return new_expr
-- betaReducerM (App (Lam var rhs) x) = do
--   let iss = extendInScopeSetList emptyInScopeSet (exprFreeVarsList rhs)
--       subst =
--         if isId var
--           then Subst iss (unitVarEnv var x) emptyVarEnv emptyVarEnv
--           else
--             if isCoVar var
--               then
--                 if not (isCoArg x)
--                   then
--                     panic "Lambda expression receiving coercion variable but does not supply coercion argument"
--                   else
--                     let (Coercion c) = x
--                      in Subst iss emptyVarEnv emptyVarEnv (unitVarEnv var c)
--               else
--                 if not (isTypeArg x)
--                   then
--                     panic "Lambda expression receiving type variable but does not supply type argument"
--                   else
--                     let (Type t) = x
--                      in Subst iss emptyVarEnv (unitVarEnv var t) emptyVarEnv
--   putMsgS "Performing BETA REDUCTION. BEFORE:"
--   putMsg $ ppr $ (App (Lam var rhs) x)
--   putMsgS "AFTER:"
--   let new_expr = substExpr subst rhs
--   putMsg $ ppr new_expr
--   return new_expr
-- betaReducerM (App (Cast (Lam var rhs) c) (Type x)) = do
--   let (tv, _, f) = fromJust $ splitForAllCo_ty_maybe c
--   -- let Just (tv, _, f) = splitForAllCo_ty_maybe c
--   let newFCoercion = substitute tv x f
--   let newTerm = substitute var x rhs
--   let newCast = Cast newTerm newFCoercion
--   return newCast
betaReducerM expr@(App (Cast e_1 c) (Type t)) = do
  let refl_c = mkReflCo Nominal t
  let new_expr = Cast (App e_1 (Type t)) (mkInstCo c refl_c)
  -- putMsgS "Performing Beta reduction on coercion type application. before:"
  -- putMsg $ ppr expr
  -- putMsgS "After:"
  -- putMsg $ ppr new_expr
  return new_expr
betaReducerM expr@(App (Let b e₁) e₂) = do
  let free_vars = exprFreeVars e₂
      bound_vars = bindersOf b
  if any (`elementOfUniqSet` free_vars) bound_vars
    then return expr
    else do
      -- putMsgS "Performing Beta reduction on let floating an application: Before"
      -- putMsg $ ppr expr
      let new_expr = Let b (App e₁ e₂)
      -- putMsgS "After:"
      -- putMsg $ ppr new_expr
      return new_expr
betaReducerM expr@(App (Cast e_1 c) e_2)
  | let (Pair s1t1 s2t2) = coercionKind c
     in isFunTy s1t1 && isFunTy s2t2 = do
      let (_, nth_1, nth_2) = decomposeFunCo c
      let sym_nth_1 = mkSymCo nth_1
      -- putMsgS "Performing Beta reduction on coercion application. before:"
      -- putMsg $ ppr expr
      let new_expr = Cast (App e_1 (Cast e_2 sym_nth_1)) nth_2
      -- putMsgS "After:"
      -- putMsg $ ppr new_expr
      return new_expr
-- betaReducerM (App (Cast (Lam var rhs) c) x) = do
--   let (_, f) = fromJust $ splitFunCo_maybe c
--   -- let Just (_, f) = splitFunCo_maybe c
--   let newTerm = substitute var x rhs
--   return $ Cast newTerm f
betaReducerM x = return x

exprIsDataConAppMaybe :: CoreExpr -> Maybe (DataCon, [Type], [CoreExpr])
exprIsDataConAppMaybe (App (Var id') (Type t)) = (,[t],[]) <$> isDataConId_maybe id'
exprIsDataConAppMaybe (App (Var id') e) = (,[],[e]) <$> isDataConId_maybe id'
exprIsDataConAppMaybe (App f (Type e))
  | Just (dc, ty_args, t_args) <- exprIsDataConAppMaybe f =
      Just (dc, ty_args ++ [e], t_args)
exprIsDataConAppMaybe (App f e)
  | Just (dc, ty_args, t_args) <- exprIsDataConAppMaybe f =
      Just (dc, ty_args, t_args ++ [e])
exprIsDataConAppMaybe _ = Nothing

getMatchingAltConMaybe :: DataCon -> [Alt Var] -> Maybe (Alt Var)
getMatchingAltConMaybe _ [] = Nothing
getMatchingAltConMaybe _ (Alt DEFAULT _ _ : _) = Nothing
getMatchingAltConMaybe dc (a@(Alt (DataAlt da) _ _) : _)
  | dc == da = Just a
getMatchingAltConMaybe dc (_ : xs) = getMatchingAltConMaybe dc xs

performSubstitutionList :: [Id] -> [CoreExpr] -> CoreExpr -> CoreExpr
performSubstitutionList [] [] rhs = rhs
performSubstitutionList (v : vs) (b : bs) rhs =
  let new_expr = performSubstitution' v b rhs
   in performSubstitutionList vs bs new_expr
performSubstitutionList _ _ _ = panic "Mismatch of let-bound variables and expressions"

betaReduceM :: (FullTransform CoreExpr a) => a -> CoreM a
betaReduceM = fullTransformM betaReducerM

betaReduceCompletelyM :: (Eq (DeBruijn a), FullTransform CoreExpr a) => a -> CoreM a
betaReduceCompletelyM = fullTransformMTillFixedPoint deBruijnize betaReducerM

-- betaReducer :: CoreExpr -> CoreExpr
-- betaReducer (App (Lam var rhs) x) = substitute var x rhs
-- betaReducer x = x
--
-- betaReduce :: (FullTransform CoreExpr a) => a -> a
-- betaReduce = fullTransform betaReducer
--
-- betaReduceCompletely :: (Eq (DeBruijn a), FullTransform CoreExpr a) => a -> a
-- betaReduceCompletely = fullTransformTillFixedPoint deBruijnize betaReducer
