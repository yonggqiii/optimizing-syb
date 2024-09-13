module Engines.BetaReduction where

import Engines.Substitution(substitute)
import GHC.Plugins
import Engines.Transform
import GHC.Core.Map.Type
import Data.Maybe

betaReducerM :: CoreExpr -> CoreM CoreExpr
betaReducerM (App (Lam var rhs) x) = return $ substitute var x rhs
betaReducerM (App (Cast (Lam var rhs) c) (Type x)) = do
  let (tv, _, f) = fromJust $ splitForAllCo_ty_maybe c
  -- let Just (tv, _, f) = splitForAllCo_ty_maybe c
  let newFCoercion = substitute tv x f
  let newTerm = substitute var x rhs
  let newCast = Cast newTerm newFCoercion
  return newCast
betaReducerM (App (Cast (Lam var rhs) c) x) = do
  let (_, f) = fromJust $ splitFunCo_maybe c
  -- let Just (_, f) = splitFunCo_maybe c
  let newTerm = substitute var x rhs
  return $ Cast newTerm f
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

