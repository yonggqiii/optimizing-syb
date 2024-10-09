module Pass.Pepsa(pepsa) where

import GHC.Plugins
import Utils
import Control.Monad
import Data.List (nub)
import Engines.BetaReduction (betaReduceCompletelyM, betaReduceCompletely)
import Engines.LeftElaboration
import Engines.InlineUnfolding
import Engines.KnownCase (CaseOfKnownCase(caseOfKnownCase))
import Engines.LetInline (LetInlinable(letInline))
import Engines.Substitution (Substitutable(substitute))
import GHC.Core.Map.Type (deBruijnize)
import Engines.Transform (FullTransform(fullTransformM))
-- | The memoized specializing pass specializes traversals.
pepsa :: Opts ->  CoreToDo
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
 - -}

pepsaModGuts :: Opts -> CorePluginPass
pepsaModGuts opts mod_guts = do
  putMsgS "PEPSA"
  let all_binds    = mg_binds mod_guts
  new_binds <- doThing 100 all_binds []
  putMsg $ ppr new_binds
  return mod_guts {mg_binds = new_binds}

doThing :: Int -> [CoreBind] -> MemoTable -> CoreM [CoreBind]
doThing 0 binds _ = return binds
doThing n binds memo = do
  i <- initialTargets binds [] binds
  i2 <- recursivelyAcquireTargets i binds
  -- showTargets i2
  (b', memo1, flag) <- transform binds i2 binds memo
  -- putMsg $ ppr memo1
  if not flag
  then putMsgS "NOTHING LEFT APPARENTLY" >> return b'
  else do (b''', ls) <- extractLetBinds b'
          let new_pgm = if not (null ls) then Rec ls : b''' else b'''
          -- putMsg $ ppr new_pgm
          doThing (n - 1) new_pgm memo1
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
listToIndices (x:xs) = listToIndices xs @+ x

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

instance RecTargetAcquirable a => RecTargetAcquirable [a] where
  recTargets [] _ _ t _ = return t
  recTargets (x:xs) lhs vs t binds = do
    t1 <- recTargets x lhs vs t binds
    recTargets xs lhs vs t1 binds

instance RecTargetAcquirable CoreExpr where
  recTargets (Let b e) _ _ targets binds = do
    t1 <- recTargets b Nothing [] targets (b : binds)
    recTargets e Nothing [] t1 (b : binds)
  recTargets (Lam b e@(Lam _ _)) (Just x) lbvs targets binds = recTargets e (Just x) (lbvs ++ [b]) targets binds
  recTargets (Lam b e) (Just x) lbvs targets binds = do
    let all_vars = lbvs ++ [b]
    appViews <- getAppViews e [] targets
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

class Transformable a where
  transform :: a -> Targets -> [CoreBind] -> MemoTable -> CoreM (a, MemoTable, Bool)

instance Transformable CoreExpr where
  transform e t binds memo
    | Just av <- getPSA e t binds = do
        -- putMsgS "FOUND"
        -- putMsg $ ppr e
        let possible_memoized = getMemoized e memo
        let in_scope_memoized = filter (`boundIn` binds) possible_memoized
        case in_scope_memoized of
          [] -> do let expr_type = exprType e
                   new_id <- mkSatLHS expr_type
                   (sated_e, memo_e) <- transformRHS av binds
                   return (Let (Rec [(new_id, sated_e)]) (Var new_id), map (, new_id) memo_e ++ memo, True)
          (x:_) -> do -- putMsgS "MEMO:"
                      -- putMsg $ ppr x
                      return (Var x, memo, True) 
        -- let expr_type = exprType e
        -- new_id <- mkSatLHS expr_type
        -- sated_e <- transformRHS av binds
        -- return (Let (Rec [(new_id, sated_e)]) (Var new_id), memo, True)
  transform (App f x) t binds memo = do
    (f', memo1, flag) <- transform f t binds memo
    if not flag
    then do (x', memo2, flag2) <- transform x t binds memo1
            return (App f' x', memo2, flag2)
    else return (App f' x, memo1, flag)
  transform (Lam b e) t binds memo = do
    (e', memo1, flag) <- transform e t binds memo
    return (Lam b e', memo1, flag)
  transform (Let b e) t binds memo = do
    (b', memo1, flag) <- transform b t (b : binds) memo
    if not flag
    then do (e', memo2, flag1) <- transform e t (b : binds) memo1
            return (Let b' e', memo2, flag1)
    else return (Let b' e, memo1, flag)
  transform (Case e b t alts) target binds memo = do
    (e', memo1, flag) <- transform e target binds memo
    if not flag
    then do (alts', memo2, flag1) <- transform alts target binds memo1
            return (Case e' b t alts', memo2, flag1)
    else return (Case e' b t alts, memo1, flag)
  transform (Cast e c) target binds memo = do
    (e', memo1, flag) <- transform e target binds memo
    return (Cast e' c, memo1, flag)
  transform (Tick t e) target binds memo = do
    (e', memo1, flag) <- transform e target binds memo
    return (Tick t e', memo1, flag)
  transform e _ _ memo = return (e, memo, False)

instance Transformable a => Transformable [a] where
  transform [] t b memo = return ([], memo, False)
  transform (x:xs) target binds memo = do
    (x', memo1, flag) <- transform x target binds memo
    if not flag
    then do (xs', memo2, flag1) <- transform xs target binds memo1
            return (x':xs', memo2, flag1)
    else return (x':xs, memo1, flag)

transformRHS :: AppView -> [CoreBind] -> CoreM (CoreExpr, [CoreExpr])
transformRHS (f, args) binds = do
  let inlined = if f `boundIn` binds 
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
  -- putMsgS "INLINED"
  -- putMsg $ ppr inlined
  let applied = foldl App inlined new_args
  beta'd <- betaReduceCompletelyM applied
  rhs <- betaReduceCompletelyM $ letInline $ caseOfKnownCase beta'd
  let original_expr = foldl App (Var f) args
  let inline_dict_expr = foldl App (Var f) memo_args
  return (rhs, [original_expr, inline_dict_expr])

inlineDict :: CoreProgram -> CoreExpr -> CoreM CoreExpr
inlineDict pgm (Var v) = do
  let lhss = pgm >>= bindersOf
  if v `elem` lhss
  then do let rhs = lookupTopLevelRHS v pgm
              av = getAppView rhs []
          case av of 
            Just (dfun, _) -> case realIdUnfolding dfun of
                                DFunUnfolding {} -> return rhs
                                _ -> return $ Var v
            Nothing -> return $ Var v
  else return $ Var v
-- inlineDict pgm (Var v)
--   = do let lhss = pgm >>= bindersOf
--        if v `elem` lhss
--        then return $ lookupTopLevelRHS v pgm 
--        else return $ Var v
inlineDict _ e = return e

lookupTopLevelRHS :: Id -> [CoreBind] -> CoreExpr
lookupTopLevelRHS id' pgm 
    = case lookupTopLevelRHS_maybe pgm of
        Just x -> x
        Nothing -> panic "the impossible happened... cannot find RHS of bind"
  where lookupTopLevelRHS_maybe :: [CoreBind] -> Maybe CoreExpr
        lookupTopLevelRHS_maybe  [] = Nothing
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

instance Transformable CoreBind where
  transform (NonRec b e) target binds memo = do
    (e', memo1, flag) <- transform e target binds memo
    return $ (NonRec b e', memo1, flag)
  transform (Rec ls) target binds memo = do
    (ls', memo1, flag) <- transform ls target binds memo
    return $ (Rec ls', memo1, flag)

instance Transformable (Id, CoreExpr) where
  transform (i, e) t b memo = do
    (e', memo1, flag) <- transform e t b memo
    return ((i, e'), memo1, flag)
  

instance Transformable (Alt Var) where
  transform (Alt a x e) t b memo = do
    (e', memo1, flag) <- transform e t b memo
    return (Alt a x e', memo1, flag)

filterAppViews :: Targets -> [AppView] -> [AppView]
filterAppViews _ [] = []
filterAppViews t ((f, as):xs) =
  let relevant_targets = filter (\(f', is) -> (f == f') && (foldr max (-9999) (indicesToList is) < length as)) t
      mapped_views = map (\(f', is) -> (f', map (as !!) (indicesToList is))) relevant_targets
  in mapped_views ++ filterAppViews t xs

whatever :: [Var] -> [CoreBind] -> AppVars -> Indices
whatever bound_vars binds (_, app_vars) = 
  let original_indices = [0..(length bound_vars - 1)]
      occurring_indices = filter (\i -> (bound_vars !! i) `elem` app_vars) original_indices
      unoccurring_vars = filter (`notElem` bound_vars) app_vars
      dynamic_vars = filter (not . isPSTerm binds) $ map Var unoccurring_vars
  in  if not (null dynamic_vars) || null occurring_indices
      then Empty
      else listToIndices occurring_indices

class TargetAcquirable a where
  initialTargets :: a -> [Var] -> [CoreBind] -> CoreM Targets

instance TargetAcquirable CoreExpr where
  initialTargets (Var v) bvs binds = do
    let t = exprType (Var v)
    let indices = typeHigherRank t
    if indices /= Empty
    then case idDetails v of
          ClassOpId _ -> return [(v, indices @+ dictArgIndex t)]
          _ -> if v `boundIn` binds 
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
  initialTargets (Case e v t alts) bvs binds = do
    t1 <- initialTargets e bvs binds
    t2 <- initialTargets alts (v : bvs) binds
    return $ t1 ++ t2
  initialTargets (Cast e c) bvs binds = initialTargets e bvs binds
  initialTargets (Tick t e) bvs binds = initialTargets e bvs binds
  initialTargets _ _ _ = return []

instance TargetAcquirable a => TargetAcquirable [a] where
  initialTargets [] _ _ = return []
  initialTargets (x:xs) bvs binds = do
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
  initialTargets (Alt _ b e) bvs binds = initialTargets e (b ++ bvs) binds

getAppView :: CoreExpr -> [CoreExpr] -> Maybe AppView
getAppView (Var v) ls = Just (v, ls)
getAppView (App f x) ls = getAppView f (x : ls)
getAppView _ _ = Nothing

getPSA :: CoreExpr -> Targets -> [CoreBind] -> Maybe AppView
getPSA e t binds = do
  (f, args) <- getAppView e []
  let filtered_t = filter (\(x, _) -> f == x) t
  psargs <- areArgsTargetsAndPS args binds filtered_t
  return (f, psargs)

areArgsTargetsAndPS :: [CoreExpr] -> [CoreBind] -> Targets -> Maybe [CoreExpr]
areArgsTargetsAndPS args binds [] = Nothing
areArgsTargetsAndPS args binds ((f, indices):xs) = do
  let is = indicesToList indices
  if foldr max (-9999) is /= length args - 1
  then areArgsTargetsAndPS args binds xs
  else do let args_that_must_be_ps = map (args !!) is
          if all (isPSTerm binds) args_that_must_be_ps
          then return args
          else areArgsTargetsAndPS args binds xs

isPSTerm :: [CoreBind] -> CoreExpr -> Bool
isPSTerm binds (Var v) = (v `boundIn` binds) ||
                          (case realIdUnfolding v of
                                DFunUnfolding {} -> True
                                CoreUnfolding {} -> True
                                _ -> False)
isPSTerm _ (Type v) = not (isTyVarTy v)
isPSTerm _ _ = True

-- getAppView (App (Var v) e) targets
--   | v `isIdTarget` targets = return $ Just (v, [e])
--   | otherwise = return Nothing
-- getAppView (App f x) targets = do
--   view <- getAppView f targets
--   return $ (\(v, ls) -> (v, ls ++ [x])) <$> view
-- getAppView _ _ = return Nothing


class AppViewObtainable a where
  getAppViews :: a -> [CoreExpr] -> Targets -> CoreM [AppView]

instance AppViewObtainable CoreExpr where
  getAppViews (Var v) acc targets
    | null acc = return []
    | v `isIdTarget` targets = return [(v, acc)]
    | otherwise = return []
  getAppViews (App f x) acc targets = do
    viewsF <- getAppViews f (x : acc) targets
    viewsX <- getAppViews x [] targets
    return $ viewsF ++ viewsX
  getAppViews (Lam b e) acc targets = getAppViews e [] targets
  getAppViews (Let b e) acc targets = do
    v1 <- getAppViews b [] targets
    v2 <- getAppViews e [] targets
    return $ v1 ++ v2
  getAppViews (Case e b t alts) acc targets = do
    v1 <- getAppViews e [] targets
    v2 <- getAppViews alts [] targets
    return $ v1 ++ v2
  getAppViews (Cast e c) acc targets = getAppViews e [] targets
  getAppViews (Tick t e) acc targets = getAppViews e [] targets
  getAppViews _ _ _ = return []

instance AppViewObtainable a => AppViewObtainable [a] where
  getAppViews ls acc targets = do
    res <- mapM (\x -> getAppViews x acc targets) ls 
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
  | Just (v, t') <- splitForAllTyVar_maybe t = appIndices (+1) (typeHigherRank t')
  | Just (_, a, r) <- splitFunTy_maybe t = 
      case splitForAllTyVar_maybe a of
        Just _ -> Empty @+ 0
        Nothing -> let something = typeHigherRank a
                   in  if something /= Empty 
                       then Empty @+ 0
                       else appIndices (+1) (typeHigherRank r)
  | otherwise = Empty

type Targets = [(Id, Indices)]

showTargets :: Targets -> CoreM ()
showTargets [] = return ()
showTargets ((v, t) : xs) = do
  putMsg $ ppr v
  putMsgS $ show $ indicesToList t
  showTargets xs

type AppView = (Id, [CoreExpr])
type AppVars = (Id, [Var])


appViewToAppVar :: AppView -> AppVars
appViewToAppVar (f, as) = (f, foldr (\x y -> case x of 
  Var v -> v : y
  _ -> y) [] as)

isIdTarget :: Id -> Targets -> Bool
isIdTarget i t = i `elem` map fst t

showAppViews :: [AppView] -> CoreM ()
showAppViews [] = return ()
showAppViews ((i, e):xs) = do
  putMsgS "APPVIEW"
  putMsg $ ppr i
  putMsg $ ppr e
  showAppViews xs



mkSatLHS :: Type -> CoreM Var
mkSatLHS t = do
  uniq1 <- getUniqueM 
  uniq2 <- getUniqueM
  let name = mkInternalName uniq1 (mkLocalOcc uniq2 (mkVarOcc "sat")) (UnhelpfulSpan UnhelpfulGenerated)
  return $ mkLocalId name Many t

leftInlineLikeCrazy :: CoreExpr -> CoreM CoreExpr
leftInlineLikeCrazy = leftElaborationLikeCrazy extractor inlineId betaReduceCompletely
  where extractor :: CoreExpr -> Maybe Id
        extractor (Var v) = Just v
        extractor _       = Nothing

type MemoTable = [(CoreExpr, Var)]

getMemoized :: CoreExpr -> MemoTable -> [Var]
getMemoized e [] = []
getMemoized e ((e', v):xs) =
  let xs' = getMemoized e xs
  in  if deBruijnize e == deBruijnize e'
      then v : xs'
      else xs'

class LetFloat a where
  extractLetBinds :: a -> CoreM (a, [(Var, CoreExpr)])

class VarOcc a where
  varOccIn :: Var -> a -> Bool

instance VarOcc CoreExpr where
  varOccIn target (Var v) = target == v
  varOccIn target (Type t) = isTyVar target && target `varOccIn` t
  varOccIn target (App f x) = target `varOccIn` f || target `varOccIn` x
  varOccIn target (Lam b e) = (b /= target) && (target `varOccIn` e)
  varOccIn target (Let b e) = 
    let binders = bindersOf b
    in (target `notElem` binders) && (target `varOccIn` b ||  target `varOccIn` e)
  varOccIn target (Case e b t alts) = target `varOccIn` e || target `varOccIn` t || target `varOccIn` alts || target == b
  varOccIn target (Cast e c) = target `varOccIn` e || (isCoVar target && (target `varOccIn` c))
  varOccIn target (Tick _ e) = target `varOccIn` e
  varOccIn target (Coercion c) = isCoVar target && (target `varOccIn` c)
  varOccIn _ _ = False

instance VarOcc a => VarOcc [a] where
  varOccIn target = any $ varOccIn target

instance VarOcc CoreBind where
  varOccIn target b = any (varOccIn target) (rhssOfBind b)

instance VarOcc (Var, CoreExpr) where
  varOccIn target (lhs, rhs) = target /= lhs && (target `varOccIn` rhs)

instance VarOcc (Alt Var) where
  varOccIn target (Alt _ vs e) = (target `notElem` vs) && (target `varOccIn` e)

instance VarOcc Type where
  varOccIn target t
    | Just v <- getTyVar_maybe t = target == v
    | Just (f, x) <- splitAppTy_maybe t = target `varOccIn` f || target `varOccIn` x
    | Just (_, a, b) <- splitFunTy_maybe t = target `varOccIn` a || target `varOccIn` b
    | Just (_, ls) <- splitTyConApp_maybe t = any (varOccIn target) ls
    | Just (v, t') <- splitForAllTyVar_maybe t = v == target || target `varOccIn` t'
    | otherwise = False

instance VarOcc Coercion where
  varOccIn target c 
    | Just v <- getCoVar_maybe c = target == v
    | Just (_, ls) <- splitTyConAppCo_maybe c = any (varOccIn target) ls
    | Just (l, r) <- splitAppCo_maybe c = target `varOccIn` l || target `varOccIn` r
    | Just (l, r) <- splitFunCo_maybe c = target `varOccIn` l || target `varOccIn` r
    | Just (v, l, r) <- splitForAllCo_maybe c = target == v || target `varOccIn` l || target `varOccIn` r
    | otherwise = False


instance LetFloat CoreExpr where
  extractLetBinds (App f x) = do
    (f', b1) <- extractLetBinds f
    (x', b2) <- extractLetBinds x
    let binds = b1 ++ b2
    return (App f' x', binds)
  extractLetBinds (Lam b e) = do
    (e', binds) <- extractLetBinds e
    if null binds 
    then return (Lam b e', [])
    else return (Lam b (Let (Rec binds) e'), [])
    -- if b `varOccIn` binds
    -- then return (Lam b (Let (Rec binds) e'), [])
    -- else return (Lam b e', binds)
  extractLetBinds (Let b e) = do
    (e', binds) <- extractLetBinds e
    (b', binds2) <- extractLetBinds b
    let all_binds = binds ++ (flattenBinds [b']) ++ binds2
    return (e', all_binds) 
  extractLetBinds (Case e v t alts) = do
    (alts', binds1) <- extractLetBinds alts
    (e', binds2) <- extractLetBinds e
    let real_binds1 = substitute v e' binds1
    return (Case e' v t alts', binds2 ++ real_binds1)
  extractLetBinds (Cast e c) = do
    (e', b) <- extractLetBinds e
    return (Cast e' c, b)
  extractLetBinds (Tick t e) = do
    (e', b) <- extractLetBinds e
    return (Tick t e', b)
  extractLetBinds v = return (v, [])
    
instance LetFloat CoreBind where
  extractLetBinds (NonRec b e) = do
    (e', binds) <- extractLetBinds e
    if null binds
    then return (NonRec b e', [])
    else return (Rec ((b, e') : binds), [])
  extractLetBinds (Rec ls) = do
    (ls', binds') <- extractLetBinds ls
    return (Rec (binds' ++ ls'), [])

instance LetFloat (Id, CoreExpr) where
  extractLetBinds (i, e) = do
    (e', b) <- extractLetBinds e
    return ((i, e'), b)

instance LetFloat a => LetFloat [a] where
  extractLetBinds [] = return ([], [])
  extractLetBinds (x:xs) = do
    (x', b1) <- extractLetBinds x
    (xs', b2) <- extractLetBinds xs
    return (x':xs', b1 ++ b2)

instance LetFloat (Alt Var) where
  extractLetBinds (Alt ac vs e) = do
    (e', b) <- extractLetBinds e
    if any (`varOccIn` b) vs
    then return (Alt ac vs (Let (Rec b) e'), [])
    else return (Alt ac vs e', b)

