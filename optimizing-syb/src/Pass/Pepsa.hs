-- {-# LANGUAGE UnicodeSyntax #-}

module Pass.Pepsa (pepsa) where

import Data.List (nub)
import Engines.BetaReduction (betaReduceCompletelyM)
import Engines.LeftElaboration
import Engines.Transform (FullTransform (fullTransformM))
import GHC.Core.Map.Type (deBruijnize)
import GHC.Plugins
import Utils

-- | The memoized specializing pass specializes traversals.
pepsa :: Opts -> CoreToDo
pepsa opts = CoreDoPluginPass "PEPSA" (pepsaModGuts opts)

{- 1. Get all targets. Idea:
 -    a. Descend into expressions keeping track of every variable and accessible nontrivial bind
 -    b. Find a var. Check:
 -        i. Var in scope of let-bound bind, or has unfolding
 -        ii. Var is higher rank
 -        iii. If var is class method, add dict arg to index
 -    c. Float back up. Descend into expressions and find
 -        i. Lam (b ...) (keep track of all bound vars). Find largest Apps
 -        ii. App of target found with indices, track which index of bs... occur in arguments. If argument has var not in BVS then skip
 -        iii. Make it a target.
 -    d. Repeat c. until fixed point
 -
 - 2. Descend into expressions:
 -    i. Find target
 -    ii. If PSA of target found, replace let f' = f ... in f'
 -    iii. inline f (spec f if class method), beta RHS.
 -    iv. Float binding as far out as possible
 -
 - 3. Repeat 1., 2. until no targets found or memo exceed
 -
 -}
pepsaModGuts :: Opts -> CorePluginPass
pepsaModGuts opts mod_guts = do
  prtSIf (debug opts) (info "Optimizing SYB")
  let all_binds = mg_binds mod_guts
  new_binds <- iterateTransformation opts all_binds []
  prtSIf (debug opts) (info "Complete. Program before transformation:")
  prtIf (debug opts) all_binds
  prtSIf (debug opts) (info "Program after transformation:")
  prtIf (debug opts) new_binds
  return mod_guts {mg_binds = new_binds}

-- | The number of iterations to perform.
type NumIterations = Int

-- | Repeatedly perform the transformation on the binds until no more targets are found or
-- the number of iterations reaches zero.
iterateTransformation ::
  -- | Plugin options
  Opts ->
  -- | The program
  CoreProgram ->
  -- | The memoization table
  MemoTable ->
  -- | The transformed program
  CoreM CoreProgram
iterateTransformation opts = aux n
  where
    n = num_iterations opts
    aux :: NumIterations -> CoreProgram -> MemoTable -> CoreM CoreProgram
    aux 0 pgm' _ = do
      prtSIf (debug opts) (warn $ "Fully exhausted all " ++ show n ++ " iterations")
      return pgm'
    aux m pgm₁ memo₁ = do
      prtSIf (debug opts) (info $ "Iteration " ++ show (n - m + 1))
      -- Step 1 is to obtain all the targets of optimization
      -- via the rules. Thus, we first obtain the initial
      -- targets (initialTargets), then repeatedly recursively obtain the
      -- targets until a fixed point (recursivelyAcquireTargets).
      i_ <- initialTargets pgm₁ [] pgm₁
      targets <- recursivelyAcquireTargets i_ pgm₁
      showTargets targets
      -- Step 2 is to perform the actual optimization on the targets.
      (pgm₂, memo₂, flag, floated_binds) <- optimize pgm₁ targets pgm₁ memo₁
      if not flag
        -- Nothing happened; it appears that we have optimized the program
        -- to a fixed point. Just return the resulting program.
        then putMsgS "NOTHING LEFT APPARENTLY" >> return pgm₂
        else do
          -- Stuff happened. Check if any new memoized bindings have been
          -- generated.
          let pgm₃ = case floated_binds of
                -- If there is nothing, then no need to add new binds.
                Nothing -> pgm₂
                -- A bind was floated out; Add that bind to the top-level program.
                Just (floated_id, floated_expr) -> NonRec floated_id floated_expr : pgm₂
          -- Continue the transformation.
          aux (m - 1) pgm₃ memo₂

-- | A list of targets, where each target is a pair of an 'Id' and a list of 'Indicies'.
type Targets = [(Id, Indices)]

recursivelyAcquireTargets :: Targets -> [CoreBind] -> CoreM Targets
recursivelyAcquireTargets targets binds = do
  t' <- recTargets binds Nothing [] targets binds
  let t = nub t'
  if t == targets
    then return t
    else recursivelyAcquireTargets t binds

data Indices = Empty | Branch Indices Int Indices deriving (Eq, Show)

listToIndices :: [Int] -> Indices
listToIndices [] = Empty
listToIndices (x : xs) = listToIndices xs @+ x

(@+) :: Indices -> Int -> Indices
Empty @+ x = Branch Empty x Empty
(Branch l v r) @+ x
  | x == v = Branch l v r
  | x < v = Branch (l @+ x) v r
  | otherwise = Branch l v (r @+ x)

appIndices :: (Int -> Int) -> Indices -> Indices
appIndices _ Empty = Empty
appIndices f (Branch l v r) = Branch (appIndices f l) (f v) (appIndices f r)

indicesToList :: Indices -> [Int]
indicesToList Empty = []
indicesToList (Branch l v r) = indicesToList l ++ (v : indicesToList r)

class RecTargetAcquirable a where
  recTargets :: a -> Maybe Id -> [Var] -> Targets -> [CoreBind] -> CoreM Targets

instance (RecTargetAcquirable a) => RecTargetAcquirable [a] where
  recTargets [] _ _ t _ = return t
  recTargets (x : xs) lhs vs t binds = do
    t1 <- recTargets x lhs vs t binds
    recTargets xs lhs vs t1 binds

instance RecTargetAcquirable CoreExpr where
  recTargets (Let b e) _ _ targets binds = do
    t1 <- recTargets b Nothing [] targets (b : binds)
    recTargets e Nothing [] t1 (b : binds)
  recTargets (Lam b e@(Lam _ _)) (Just x) lbvs targets binds = recTargets e (Just x) (lbvs ++ [b]) targets binds
  recTargets (Lam b e) (Just x) lbvs targets binds = do
    let all_vars = lbvs ++ [b]
    appViews <- getAppViews e [] targets Nothing
    let appViews' = filterAppViews targets appViews
    let appVars = map appViewToAppVar appViews'
    let new_targets = map (x,) $ filter (/= Empty) $ map (whatever all_vars binds) appVars
    recTargets e Nothing [] (new_targets ++ targets) binds -- has binding
  recTargets (Lam _ e) _ _ targets binds = recTargets e Nothing [] targets binds -- no binding
  recTargets (App f x) _ _ targets binds = do
    t1 <- recTargets f Nothing [] targets binds
    recTargets x Nothing [] t1 binds
  recTargets (Case e _ _ alts) _ _ targets binds = do
    t1 <- recTargets e Nothing [] targets binds
    recTargets alts Nothing [] t1 binds
  recTargets (Cast e _) _ _ targets binds = recTargets e Nothing [] targets binds
  recTargets (Tick _ e) _ _ targets binds = recTargets e Nothing [] targets binds
  recTargets _ _ _ targets _ = return targets

instance RecTargetAcquirable CoreBind where
  recTargets (NonRec b e) _ _ targets binds = recTargets e (Just b) [] targets binds
  recTargets (Rec ls) _ _ targets binds = recTargets ls Nothing [] targets binds

instance RecTargetAcquirable (Id, CoreExpr) where
  recTargets (b, e) _ _ = recTargets e (Just b) []

instance RecTargetAcquirable (Alt Var) where
  recTargets (Alt _ _ e) _ _ = recTargets e Nothing []

type InScopeBinds = [CoreBind]

type NewMemoTable = MemoTable

type IsTransformed = Bool

type FloatedBind = (Id, CoreExpr)

class Optimizable a where
  -- | Performs the actual transformation on the term.
  optimize ::
    -- | The thing to transform
    a ->
    -- | The targets to look for
    Targets ->
    -- | The in-scope binds at that program point (used to check if a memoized
    -- expression is in scope)
    InScopeBinds ->
    -- | The memoization table
    MemoTable ->
    -- | The transformed expression, the new memoization table, whether it was
    -- transformed, and any floated binding. The 'IsTransformed' flag is required
    -- as they may be no floated binding, but the expression may still be
    -- transformed.
    -- Invariant 1: If 'IsTransformed' is 'False', then the 'FloatedBind' is
    -- 'Nothing'.
    -- Invariant 2: As long as the target of transformation has been changed
    -- in any way, the 'IsTransformed' flag is 'True'.
    CoreM (a, NewMemoTable, IsTransformed, Maybe FloatedBind)

instance Optimizable CoreExpr where
  -- The case where a transformation can be performed.
  optimize expr targets in_scope_binds memo
    -- Getting the partially static application yielded a successful result.
    | Just app_view <- getPSA expr targets in_scope_binds = do
        putMsgS "Target found!"
        putMsg $ ppr expr
        -- Check to see if the expression is already memoized
        let possible_memoized = getMemoized expr memo
            -- Make sure that the memoized expressions are in scope
            in_scope_memoized =
              filter
                (`boundIn` in_scope_binds)
                possible_memoized
        case in_scope_memoized of
          [] -> do
            -- If not memoized, create a new binding
            -- Get the type of the expression
            let expr_type = exprType expr
            -- Create a new identifier for the binding
            new_id <- mkSatLHS expr_type
            -- Transform the expression (it is an application view)
            (sated_e, memo_e) <- transformRHS app_view in_scope_binds
            -- The floated bind is the new identifier and the transformed
            -- expression
            let floated_bind = (new_id, sated_e)
                -- Add a new entry to the memoization table
                new_memo = map (,new_id) memo_e ++ memo
                -- The new expression is just the new identifier generated.
                new_expr = Var new_id
            return (new_expr, new_memo, True, Just floated_bind)
          -- If it is already memoized, just return the variable
          (x : _) -> return (Var x, memo, True, Nothing)
  optimize (App f x) targets in_scope_binds memo = do
    -- Pretty simple since an application introduces no bindings. Whatever
    -- let-bind is generated can be simply floated out.
    (f', memo₁, flag₁, floated_binds₁) <- optimize f targets in_scope_binds memo
    if flag₁
      then do
        -- If the function was transformed, we should not transform the argument.
        -- Just return the application with the transformed function.
        -- case floated_binds₁ of
        --   Nothing -> return ()
        --   Just ff -> do
        --     putMsgS "FLOATING"
        --     putMsg $ ppr ff
        --     putMsgS "out of"
        --     putMsg $ ppr $ App f' x
        return (App f' x, memo₁, True, floated_binds₁)
      else do
        -- Since there is nothing to do for the function, we can just transform
        -- the argument.
        (x', memo₂, flag₂, floated_binds₂) <-
          optimize
            x
            targets
            in_scope_binds
            memo₁
        -- case floated_binds₂ of
        --   Nothing -> return ()
        --   Just ff -> do
        --     putMsgS "FLOATING"
        --     putMsg $ ppr ff
        --     putMsgS "out of"
        --     putMsg $ ppr $ App f' x'
        return (App f' x', memo₂, flag₂, floated_binds₂)
  optimize (Lam b e) targets in_scope_binds memo = do
    -- Transform the function body.
    (e', memo', flag, floated_binds) <- optimize e targets in_scope_binds memo
    -- Check if there is nothing to do
    if not flag
      then do
        -- case floated_binds of
        --   Nothing -> return ()
        --   Just ff -> do
        --     putMsgS "FLOATING"
        --     putMsg $ ppr ff
        --     putMsgS "out of"
        --     putMsg $ ppr $ Lam b e'
        return (Lam b e', memo', False, floated_binds)
      else case floated_binds of
        -- Something happened.
        -- If there is no floated bind, just return the lambda with the transformed body.
        Nothing -> return (Lam b e', memo', True, Nothing)
        -- If there is a floated bind, check if it can also be floated
        -- again. The way to do so is to check if the expression's free variables
        -- includes the variable bound by the lambda.
        Just (floated_id, floated_expr) ->
          if b `elementOfUniqSet` exprFreeVars floated_expr
            then
              -- Cannot float again because the variable bound by the lambda
              -- is used in the RHS of the let bind, so just return the lambda
              -- with the let binding.
              return (Lam b (Let (NonRec floated_id floated_expr) e'), memo', True, Nothing)
            else do
              -- putMsgS "FLOATING"
              -- putMsg $ ppr (floated_id, floated_expr)
              -- putMsgS "out of"
              -- putMsg $ ppr $ Lam b e'
              -- Can continue to float the let binding, so return the lambda
              -- that does not contain the let binding
              return (Lam b e', memo', True, floated_binds)
  optimize (Let b e) targets in_scope_binds memo = do
    -- Transform the bindings. Ensure that all the bindings are made in scope.
    (b', memo₁, flag₁, floated_binds₁) <-
      optimize
        b
        targets
        (b : in_scope_binds)
        memo
    if flag₁
      -- Something happened.
      -- The handling of the floated binds should be done by the transformation
      -- of the binds. Just directly return.
      then return (Let b' e, memo₁, True, floated_binds₁)
      else do
        -- If there is nothing to do, just transform the expression. Same
        -- thing: make sure the let bindings are in scope.
        (e', memo₂, flag₂, floated_binds₂) <- optimize e targets (b : in_scope_binds) memo₁
        -- Now check if there is a floated bind from transforming the expression.
        case floated_binds₂ of
          Nothing -> return (Let b' e', memo₂, flag₂, Nothing)
          Just (floated_id, floated_expr) -> do
            -- If there is a floated bind, we should check if it can be floated
            -- further.
            -- Get all the let-bound variables in the let binding.
            let introduced_vars = bindersOf b'
                -- Get all the free variables in the expression
                free_vars = exprFreeVars floated_expr
            -- Check if any of the let-bound vars are free vars in the expression.
            if any (`elementOfUniqSet` free_vars) introduced_vars
              -- If so, we cannot float it further, so we just include the
              -- floated bind in the let binding. Note that the
              -- resulting binding is a recursive binding.
              then case b' of
                NonRec x y -> return (Let (Rec [(floated_id, floated_expr), (x, y)]) e', memo₂, True, Nothing)
                Rec ls -> return (Let (Rec ((floated_id, floated_expr) : ls)) e', memo₂, True, Nothing)
              else
                -- If not, we can float it further.
                return (Let b' e', memo₂, True, floated_binds₂)
  optimize (Case e b t alts) targets in_scope_binds memo = do
    -- Perform the transformation on the expression.
    (e', memo₁, flag₁, floated_binds₁) <- optimize e targets in_scope_binds memo
    if flag₁
      then
        -- It was transformed; just float out the floated binds.
        return (Case e' b t alts, memo₁, True, floated_binds₁)
      else do
        -- If there is nothing to do, just transform the alts.
        (alts', memo₂, flag₂, floated_binds₂) <- optimize alts targets in_scope_binds memo₁
        -- Check if b occurs in the floated binds.
        case floated_binds₂ of
          Nothing -> return (Case e' b t alts', memo₂, flag₂, floated_binds₂)
          Just (floated_id, floated_expr) ->
            let free_vars = exprFreeVars floated_expr
             in if b `elementOfUniqSet` free_vars
                  -- Cannot float out, so it is a little bit tricky. Best way
                  -- to proceed is to put a let binding with the expression
                  -- and the bind.
                  then
                    return
                      ( Let
                          (Rec [(floated_id, floated_expr), (b, e')])
                          (Case e' b t alts'),
                        memo₂,
                        flag₂,
                        Nothing
                      )
                  else return (Case e' b t alts', memo₂, flag₂, floated_binds₂)
  optimize (Cast e c) targets in_scope_binds memo = do
    -- Very straightforward: just transform the expression.
    (e', memo', flag, floated_binds) <- optimize e targets in_scope_binds memo
    return (Cast e' c, memo', flag, floated_binds)
  optimize (Tick t e) targets in_scope_binds memo = do
    -- Very straightforward: just transform the expression.
    (e', memo', flag, floated_binds) <- optimize e targets in_scope_binds memo
    return (Tick t e', memo', flag, floated_binds)
  -- For all other cases, there is nothing to do!
  optimize e _ _ memo = return (e, memo, False, Nothing)

instance Optimizable (Alt Var) where
  optimize (Alt alt_con b e) targets in_scope_binds memo = do
    (e', memo', flag, floated_binds) <- optimize e targets in_scope_binds memo
    case floated_binds of
      Nothing -> return (Alt alt_con b e', memo', flag, Nothing)
      Just (floated_id, floated_expr) -> do
        -- If there is a floated bind, we should check if it can be floated
        -- further.
        -- Get all the free variables in the floated expression.
        let free_vars = exprFreeVars floated_expr
        -- Check if any of the alt-bound variables are free variables in the expression.
        if any (`elementOfUniqSet` free_vars) b
          -- If so, we cannot float it further, so we put the floated binds
          -- in a let binding.
          then return (Alt alt_con b (Let (NonRec floated_id floated_expr) e'), memo', True, Nothing)
          -- can float it further!
          else return (Alt alt_con b e', memo', True, floated_binds)

instance Optimizable CoreBind where
  optimize (NonRec b e) targets in_scope_binds memo = do
    (e', memo', flag, floated_binds) <- optimize e targets in_scope_binds memo
    case floated_binds of
      -- No binds to float out; just return the let binding with the
      -- transformed body.
      Nothing -> return (NonRec b e', memo', flag, Nothing)
      -- There is a floated bind, so we should check if it can be
      -- floated further.
      Just (floated_id, floated_expr) -> do
        -- Get all the free variables in the expression
        let free_vars = exprFreeVars floated_expr
        -- Check if any of the let-bound vars are free vars in the
        -- expression.
        if b `elementOfUniqSet` free_vars
          -- If so, we cannot float it further, so we just include the
          -- floated bind in the let binding. Note that the
          -- resulting binding is a recursive binding.
          then return (Rec [(floated_id, floated_expr), (b, e)], memo', True, Nothing)
          -- If not, we can float it further.
          else return (NonRec b e', memo', True, floated_binds)
  optimize (Rec ls) targets in_scope_binds memo = do
    (ls', memo', flag, floated_binds) <- optimize ls targets in_scope_binds memo
    case floated_binds of
      -- No binds to float out; just return the let binding with the
      -- transformed body.
      Nothing -> return (Rec ls', memo', flag, Nothing)
      -- There is a floated bind, so we should check if it can be
      -- floated further.
      Just (floated_id, floated_expr) -> do
        -- If there is a floated bind, we should check if it can be floated
        -- further.
        -- Get all the let-bound variables in the let binding.
        let introduced_vars = bindersOf (Rec ls')
            -- Get all the free variables in the expression
            free_vars = exprFreeVars floated_expr
        -- Check if any of the let-bound vars are free vars in the expression.
        if any (`elementOfUniqSet` free_vars) introduced_vars
          -- If so, we cannot float it further, so we just include the
          -- floated bind in the let binding. Note that the
          -- resulting binding is a recursive binding.
          then return (Rec ((floated_id, floated_expr) : ls'), memo', flag, Nothing)
          -- If not, we can float it further.
          else
            return (Rec ls', memo', True, floated_binds)

instance (Optimizable a) => Optimizable [a] where
  optimize [] _ _ memo = return ([], memo, False, Nothing)
  optimize (x : xs) targets in_scope_binds memo = do
    (x', memo1, flag, floated_binds) <- optimize x targets in_scope_binds memo
    if not flag
      then do
        (xs', memo2, flag2, floated_binds2) <- optimize xs targets in_scope_binds memo1
        return (x' : xs', memo2, flag2, floated_binds2)
      else return (x' : xs, memo1, flag, floated_binds)

instance Optimizable (Id, CoreExpr) where
  optimize (i, e) targets in_scope_binds memo = do
    (e', memo1, flag, floated_binds) <- optimize e targets in_scope_binds memo
    return ((i, e'), memo1, flag, floated_binds)

transformRHS :: AppView -> [CoreBind] -> CoreM (CoreExpr, [CoreExpr])
transformRHS (f, args, recover) binds = do
  let inlined =
        if f `boundIn` binds
          then lookupTopLevelRHS f binds
          else unfoldingTemplate $ realIdUnfolding f
  memo_args <- mapM (fullTransformM (inlineDict binds)) args
  new_args <- case idDetails f of
    ClassOpId {} -> do
      let t = idType f
          i = dictArgIndex t
          d_arg = memo_args !! i
      dictArg <- leftInlineLikeCrazy d_arg
      return $ take i memo_args ++ (dictArg : drop (i + 1) memo_args)
    _ -> return memo_args
  let applied = foldl App (recover inlined) new_args
  beta'd <- betaReduceCompletelyM applied
  let original_expr = foldl App (Var f) args
  let inline_dict_expr = foldl App (Var f) memo_args
  return (beta'd, [original_expr, inline_dict_expr])

inlineDict :: CoreProgram -> CoreExpr -> CoreM CoreExpr
inlineDict pgm (Var v) = do
  let lhss = pgm >>= bindersOf
  if v `elem` lhss
    then do
      let rhs = lookupTopLevelRHS v pgm
          av = getAppView rhs [] Nothing
      case av of
        Just (dfun, _, _) -> case realIdUnfolding dfun of
          DFunUnfolding {} -> return rhs
          _ -> return $ Var v
        Nothing -> return $ Var v
    else return $ Var v
inlineDict _ e = return e

lookupTopLevelRHS :: Id -> [CoreBind] -> CoreExpr
lookupTopLevelRHS id' pgm =
  case lookupTopLevelRHS_maybe pgm of
    Just x -> x
    Nothing -> panic "the impossible happened... cannot find RHS of bind"
  where
    lookupTopLevelRHS_maybe :: [CoreBind] -> Maybe CoreExpr
    lookupTopLevelRHS_maybe [] = Nothing
    lookupTopLevelRHS_maybe (NonRec lhs rhs : bs)
      | id' == lhs = Just rhs
      | otherwise = lookupTopLevelRHS_maybe bs
    lookupTopLevelRHS_maybe (Rec ls : bs) =
      case aux ls of
        Nothing -> lookupTopLevelRHS_maybe bs
        x -> x
    aux :: [(Id, CoreExpr)] -> Maybe CoreExpr
    aux [] = Nothing
    aux ((lhs, rhs) : rs)
      | id' == lhs = Just rhs
      | otherwise = aux rs

filterAppViews :: Targets -> [AppView] -> [AppView]
filterAppViews _ [] = []
filterAppViews t ((f, as, recover) : xs) =
  let relevant_targets = filter (\(f', is) -> (f == f') && (foldr max (-9999) (indicesToList is) < length as)) t
      mapped_views = map (\(f', is) -> (f', map (as !!) (indicesToList is), recover)) relevant_targets
   in mapped_views ++ filterAppViews t xs

whatever :: [Var] -> [CoreBind] -> AppVars -> Indices
whatever bound_vars binds (_, app_vars) =
  let original_indices = [0 .. (length bound_vars - 1)]
      occurring_indices = filter (\i -> (bound_vars !! i) `elem` app_vars) original_indices
      unoccurring_vars = filter (`notElem` bound_vars) app_vars
      dynamic_vars = filter (not . isPSTerm binds) $ map Var unoccurring_vars
   in if not (null dynamic_vars) || null occurring_indices
        then Empty
        else listToIndices occurring_indices

class TargetAcquirable a where
  initialTargets :: a -> [Var] -> [CoreBind] -> CoreM Targets

instance TargetAcquirable CoreExpr where
  initialTargets (Var v) _ binds = do
    let t = exprType (Var v)
    let indices = typeHigherRank t
    if indices /= Empty
      then case idDetails v of
        ClassOpId {} -> return [(v, indices @+ dictArgIndex t)]
        _ ->
          if v `boundIn` binds
            then return [(v, indices)]
            else case realIdUnfolding v of
              CoreUnfolding {} -> return [(v, indices)]
              _ -> return []
      else return []
  initialTargets (App f x) bvs binds = do
    t1 <- initialTargets f bvs binds
    t2 <- initialTargets x bvs binds
    return $ t1 ++ t2
  initialTargets (Lam b e) bvs binds = initialTargets e (b : bvs) binds
  initialTargets (Let b e) bvs binds = do
    t1 <- initialTargets e bvs (b : binds)
    t2 <- initialTargets b bvs (b : binds)
    return $ t1 ++ t2
  initialTargets (Case e v _ alts) bvs binds = do
    t1 <- initialTargets e bvs binds
    t2 <- initialTargets alts (v : bvs) binds
    return $ t1 ++ t2
  initialTargets (Cast e _) bvs binds = initialTargets e bvs binds
  initialTargets (Tick _ e) bvs binds = initialTargets e bvs binds
  initialTargets _ _ _ = return []

instance (TargetAcquirable a) => TargetAcquirable [a] where
  initialTargets [] _ _ = return []
  initialTargets (x : xs) bvs binds = do
    t1 <- initialTargets x bvs binds
    t2 <- initialTargets xs bvs binds
    return $ t1 ++ t2

instance TargetAcquirable CoreBind where
  initialTargets (NonRec b e) bvs binds = do
    t1 <- initialTargets (Var b :: CoreExpr) bvs binds
    t2 <- initialTargets e bvs binds
    return $ t1 ++ t2
  initialTargets (Rec ls) bvs binds = initialTargets ls bvs binds

instance TargetAcquirable (Id, CoreExpr) where
  initialTargets (b, e) bvs binds = do
    t1 <- initialTargets (Var b :: CoreExpr) bvs binds
    t2 <- initialTargets e bvs binds
    return $ t1 ++ t2

instance TargetAcquirable (Alt Var) where
  initialTargets (Alt _ b e) bvs = initialTargets e (b ++ bvs)

getAppView :: CoreExpr -> [CoreExpr] -> Maybe (CoreExpr -> CoreExpr) -> Maybe AppView
getAppView (Var _) [] _ = Nothing
getAppView (Var v) ls Nothing = Just (v, ls, id)
getAppView (Var v) ls (Just f) = Just (v, ls, f)
getAppView (App f x) ls _ = getAppView f (x : ls) Nothing
getAppView (Cast _ _) [] _ = Nothing
getAppView (Cast e c) ls Nothing = getAppView e ls (Just (`Cast` c))
getAppView (Cast e c) ls (Just f) = getAppView e ls (Just (f . (`Cast` c)))
getAppView _ _ _ = Nothing

getPSA :: CoreExpr -> Targets -> [CoreBind] -> Maybe AppView
getPSA e t binds = do
  (f, args, recover) <- getAppView e [] Nothing
  let filtered_t = filter (\(x, _) -> f == x) t
  psargs <- areArgsTargetsAndPS args binds filtered_t
  return (f, psargs, recover)

areArgsTargetsAndPS :: [CoreExpr] -> [CoreBind] -> Targets -> Maybe [CoreExpr]
areArgsTargetsAndPS _ _ [] = Nothing
areArgsTargetsAndPS args binds ((_, indices) : xs) = do
  let is = indicesToList indices
  if foldr max (-9999) is /= length args - 1
    then areArgsTargetsAndPS args binds xs
    else do
      let args_that_must_be_ps = map (args !!) is
      if all (isPSTerm binds) args_that_must_be_ps
        then return args
        else areArgsTargetsAndPS args binds xs

isPSTerm :: [CoreBind] -> CoreExpr -> Bool
isPSTerm binds (Var v) =
  (v `boundIn` binds)
    || ( case realIdUnfolding v of
           DFunUnfolding {} -> True
           CoreUnfolding {} -> True
           _ -> False
       )
isPSTerm _ (Type v) = not (isTyVarTy v)
isPSTerm _ _ = True

class AppViewObtainable a where
  getAppViews :: a -> [CoreExpr] -> Targets -> Maybe (CoreExpr -> CoreExpr) -> CoreM [AppView]

instance AppViewObtainable CoreExpr where
  getAppViews (Var v) acc targets Nothing
    | null acc = return []
    | v `isIdTarget` targets = return [(v, acc, id)]
    | otherwise = return []
  getAppViews (Var v) acc targets (Just recover)
    | null acc = return []
    | v `isIdTarget` targets = return [(v, acc, recover)]
    | otherwise = return []
  getAppViews (App f x) acc targets _ = do
    viewsF <- getAppViews f (x : acc) targets Nothing
    viewsX <- getAppViews x [] targets Nothing
    return $ viewsF ++ viewsX
  getAppViews (Lam _ e) _ targets _ = getAppViews e [] targets Nothing
  getAppViews (Let b e) _ targets _ = do
    v1 <- getAppViews b [] targets Nothing
    v2 <- getAppViews e [] targets Nothing
    return $ v1 ++ v2
  getAppViews (Case e _ _ alts) _ targets _ = do
    v1 <- getAppViews e [] targets Nothing
    v2 <- getAppViews alts [] targets Nothing
    return $ v1 ++ v2
  getAppViews (Cast e _) [] targets _ = getAppViews e [] targets Nothing
  getAppViews (Cast e c) acc targets Nothing = getAppViews e acc targets (Just (`Cast` c))
  getAppViews (Cast e c) acc targets (Just recover) = getAppViews e acc targets (Just (recover . (`Cast` c)))
  getAppViews (Tick _ e) _ targets _ = getAppViews e [] targets Nothing
  getAppViews _ _ _ _ = return []

instance (AppViewObtainable a) => AppViewObtainable [a] where
  getAppViews ls acc targets _ = do
    res <- mapM (\x -> getAppViews x acc targets Nothing) ls
    return $ concat res

instance AppViewObtainable CoreBind where
  getAppViews b _ = getAppViews (rhssOfBind b) []

instance AppViewObtainable (Alt Var) where
  getAppViews (Alt _ _ e) _ = getAppViews e []

dictArgIndex :: Type -> Int
dictArgIndex t
  | Just (_, t') <- splitForAllTyVar_maybe t = dictArgIndex t' + 1
  | Just _ <- splitFunTy_maybe t = 0
  | otherwise = panic "Impossible! Function is supposed to receive dictionary argument but does not!"

boundIn :: Id -> [CoreBind] -> Bool
boundIn _ [] = False
boundIn v (NonRec v' _ : xs)
  | v == v' = True
  | otherwise = v `boundIn` xs
boundIn v (Rec ls : xs) = v `elem` map fst ls || v `boundIn` xs

typeHigherRank :: Type -> Indices
typeHigherRank t
  | Just (_, t') <- splitForAllTyVar_maybe t = appIndices (+ 1) (typeHigherRank t')
  | Just (_, _, a, r) <- splitFunTy_maybe t =
      case splitForAllTyVar_maybe a of
        Just _ -> Empty @+ 0
        Nothing ->
          let something = typeHigherRank a
           in if something /= Empty
                then Empty @+ 0
                else appIndices (+ 1) (typeHigherRank r)
  | otherwise = Empty

showTargets :: Targets -> CoreM ()
showTargets [] = return ()
showTargets ((v, t) : xs) = do
  putMsg $ ppr v
  putMsgS $ show $ indicesToList t
  showTargets xs

type AppView = (Id, [CoreExpr], CoreExpr -> CoreExpr)

type AppVars = (Id, [Var])

appViewToAppVar :: AppView -> AppVars
appViewToAppVar (f, as, _) =
  ( f,
    foldr
      ( \x y -> case x of
          Var v -> v : y
          _ -> y
      )
      []
      as
  )

isIdTarget :: Id -> Targets -> Bool
isIdTarget i t = i `elem` map fst t

-- | Creates a new identifier for the LHS of a generated bind.
mkSatLHS ::
  -- | The type of the WithHsDocIdentifiers
  Type ->
  -- | The identifier itself.
  CoreM Id
mkSatLHS t = do
  -- get the unique values from the monad
  uniq1 <- getUniqueM
  uniq2 <- getUniqueM
  -- Make the name. The name is a local occurrence and should not have to be
  -- exported (it will likely be a local variable). We just use
  -- 'UnhelpfulSpan' and 'UnhelpfulGenerated' since this ID is generated
  -- by us.
  let name = mkInternalName uniq1 (mkLocalOcc uniq2 (mkVarOcc "sat_OptimizingSYB")) (UnhelpfulSpan UnhelpfulGenerated)
  -- The multiplicity is 'ManyTy' because, well, who cares.
  return $ mkLocalId name ManyTy t

leftInlineLikeCrazy :: CoreExpr -> CoreM CoreExpr
leftInlineLikeCrazy = leftElaborationLikeCrazy extractor inlineId
  where
    extractor :: CoreExpr -> Maybe Id
    extractor (Var v) = Just v
    extractor _ = Nothing
    inlineId :: Id -> CoreM CoreExpr
    inlineId v = do
      let uf = realIdUnfolding v
      case uf of
        DFunUnfolding bndrs df_con df_args -> do
          let dfune = mkCoreConApps df_con df_args
          let dfun = foldr Lam dfune bndrs
          return dfun
        CoreUnfolding tmpl _ _ _ _ -> do
          return tmpl
        OtherCon _ -> do
          return $ Var v
        NoUnfolding -> do
          return $ Var v
        _ -> do
          return $ Var v

type MemoTable = [(CoreExpr, Var)]

getMemoized :: CoreExpr -> MemoTable -> [Var]
getMemoized _ [] = []
getMemoized e ((e', v) : xs) =
  let xs' = getMemoized e xs
   in if deBruijnize e == deBruijnize e'
        then v : xs'
        else xs'
