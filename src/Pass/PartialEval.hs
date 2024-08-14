module Pass.PartialEval(specByPartialEvaluation) where
import GHC.Plugins
    ( CoreToDo(CoreDoPluginPass),
      ModGuts(mg_binds),
      falseDataCon,
      trueDataCon,
      mkCoreConApps,
      putMsg,
      putMsgS,
      getTyVar_maybe,
      isTyVarTy,
      splitTyConApp_maybe,
      nameStableString,
      Alt(Alt),
      Bind(Rec, NonRec),
      CoreBind,
      Expr(..),
      CoreM,
      CorePluginPass,
      Type,
      Var(varName),
      Outputable(ppr) )
import Control.Monad ( guard, when )
import Data.Maybe ( isJust )

{- The idea behind this pass is to evaluate checks for type-equality 
 - at compile-time. This enables us to eliminate the run-time type 
 - equality checks that slows down the program, especially because 
 - in many cases, the types are already fully-determined at compile time 
 - as revealed by earlier passes.
 -
 - This pass is relatively simple:
 -    1.  Traverse every single CoreBind and look for any occurrences of 
 -        sameTypeRep @k1 @k2 @T1 @T2 x y 
 -    2.  Partially evaluate those expressions, giving True, False. 
 -
 - However, not every expression of that form can be evaluated. Particularly,
 - there will be cases where the arguments are type variables and should be 
 - evaluated at run-time. We summarize the rules for evaluating these expressions
 - as follows. For an expression sameTypeRep @k1 @k2 @T1 @T2 x y:
 -    1.  If k1 == k2 and T1 == T2, rewrite the entire expression to True 
 -    2.  If T1 /= T2 and neither of these are type variables, rewrite the 
 -        entire expression to False 
 -    3.  Otherwise, expression remains intact.
 -
 - In the future, we will want to handle the more general case of any function
 - application or type-level evaluation that can be done at compile-time, and 
 - not just sameTypeRep. -}

-- | The 'specByPartialEvaluation' pass traverses through the entire program and searches
-- occurrences of 'sameTypeRep' that can be evaluated at compile time, and replaces 
-- them with their evaluations.
specByPartialEvaluation :: CoreToDo
specByPartialEvaluation = CoreDoPluginPass "Specialization by Partial Evaluation" partialEvalModGuts

-- | Performs specialization by partial evaluation on 'ModGuts'
partialEvalModGuts :: CorePluginPass
partialEvalModGuts mod_guts = do
  putMsgS "== Phase: Specialization by Partial Evaluation =="
  -- First, get all the CoreBinds in the program
  let all_core_binds :: [CoreBind] = mg_binds mod_guts
  all_new_core_binds :: [CoreBind] <- mapM partialEvalCoreBind all_core_binds
  -- For now, map all the core binds with the partialEvalCoreBind function
  let new_mod_guts   :: ModGuts = mod_guts { mg_binds = all_new_core_binds }
  -- Once the mod guts have been transformed, return
  return new_mod_guts

-- | Partially evaluate a single 'CoreBind'. 
partialEvalCoreBind :: CoreBind -- ^ 'CoreBind' which we will partially evaluate
                    -> CoreM CoreBind -- ^ The resulting 'CoreBind' where partial evaluation has taken place
-- Here we are just destructuring the binds into the var names and the expr.
-- Nothing particularly special happens here. We just want to traverse into the 
-- expressions and find our target
partialEvalCoreBind (NonRec var expr) = do
  (v, e) <- partialEvalSingleBind var expr
  return $ NonRec v e
partialEvalCoreBind (Rec ls) = do
  ls' <- mapM (uncurry partialEvalSingleBind) ls
  return $ Rec ls'

-- | Traverse the RHS of the 'CoreBind'
partialEvalSingleBind :: Var -> Expr Var -> CoreM (Var, Expr Var)
partialEvalSingleBind var expr = do
  expr' <- partialEvalExpr expr
  return (var, expr')

{- This is the part that actually matters. Here, we are traversing 
 - through an expression in search for the target expression. Once 
 - it is found, we perform partial evaluation based on the rules 
 - presented above. -}
-- | Partially evaluate an 'Expr'.
partialEvalExpr :: Expr Var -- ^ The expression to evaluate 
                -> CoreM (Expr Var) -- ^ The updated expression after partial 
                                    -- evaluation (if it happened)
{- This is the most interesting case. -}
partialEvalExpr expr@(App (App (App (App (App (App (Var f) (Type _)) _) (Type t1)) (Type t2)) _) _)
    | fn_name == target_fn = do
        -- check if type applications are provably equivalent
        if provablyEquivalentTypes t1 t2 then do
          putMsgS "******* TARGET EXPRESSION FOUND *******"
          putMsg $ ppr expr
          putMsgS "REWRITE: type arguments provably equal."
          putMsgS "New expression:"
          -- If type applications are provably equivalent, emit True
          let new_expr = mkCoreConApps trueDataCon []
          putMsg $ ppr new_expr
          return new_expr
        -- check if type applications are provably distinct
        else if provablyDistinctTypes t1 t2 then do
          putMsgS "******* TARGET EXPRESSION FOUND *******"
          putMsg $ ppr expr
          putMsgS "REWRITE: type arguments provably false."
          putMsgS "New expression:"
          -- If type applications are provably distinct, emit False
          let new_expr = mkCoreConApps falseDataCon []
          putMsg $ ppr new_expr
          return new_expr
        else 
          -- Don't rewrite
          return expr
  where fn_name = nameStableString $ varName f
        target_fn = "$base$Data.Typeable.Internal$sameTypeRep"
        

-- In all other cases, traverse the expression looking for the 
-- target expression
partialEvalExpr e@(Var _) = return e
partialEvalExpr e@(Lit _) = return e
partialEvalExpr (App f x) = do
  f' <- partialEvalExpr f
  x' <- partialEvalExpr x
  return $ App f' x'
partialEvalExpr (Lam var expr) = do
  e' <- partialEvalExpr expr
  return $ Lam var e'
partialEvalExpr (Case expr var ty alts) = do
  e' <- partialEvalExpr expr
  alts' <- mapM g alts
  return $ Case e' var ty alts'
 where g (Alt alt_con names exprb) = do
        exprb' <- partialEvalExpr exprb
        return $ Alt alt_con names exprb'
partialEvalExpr (Let bind expr) = do
  bind' <- partialEvalCoreBind bind
  expr' <- partialEvalExpr expr
  return $ Let bind' expr'
partialEvalExpr (Cast expr coercion) = do
  e' <- partialEvalExpr expr
  return $ Cast e' coercion
partialEvalExpr (Tick ct e) = do
  e' <- partialEvalExpr e
  return $ Tick ct e'
partialEvalExpr e@(Type _) = return e
partialEvalExpr e@(Coercion _) = return e

-- | A function to determine if two types are provably equivalent. 
provablyEquivalentTypes :: Type -> Type -> Bool
provablyEquivalentTypes t1 t2 =
  let res 
        | not (isTyVarTy t1) && not (isTyVarTy t2) = do 
            -- t1 and t2 are concrete types. First, split the
            -- Types into TyCon and [Type] arguments
            (tc1, args1) <- splitTyConApp_maybe t1
            (tc2, args2) <- splitTyConApp_maybe t2
            -- Both type constructors must be equal
            guard (tc1 == tc2)
            -- They must both have the same number of arguments
            guard (length args1 == length args2)
            -- All the arguments must be provably equivalent
            guard $ and $ zipWith provablyEquivalentTypes args1 args2
        | isTyVarTy t1 && isTyVarTy t2 = do
            -- t1 and t2 are both type variables. First, get the 
            -- respective type variables
            tv1 <- getTyVar_maybe t1
            tv2 <- getTyVar_maybe t2
            -- The type variables must be equal for all of them to be equal.
            guard $ tv1 == tv2
        | otherwise = Nothing -- in all other cases, no proof can be shown.
  in isJust res

-- | A function to determine if two types are provably distinct.
provablyDistinctTypes :: Type -> Type -> Bool
provablyDistinctTypes t1 t2 = 
  let res | not (isTyVarTy t1) && not (isTyVarTy t2) = do
              -- t1 and t2 are concrete types. First, split the 
              -- Types into TyCon and [Type] arguments
              (tc1, args1) <- splitTyConApp_maybe t1
              (tc2, args2) <- splitTyConApp_maybe t2
              -- If tc1 /= tc2 or their lengths differ, immediately 
              -- show that they are distinct
              when (tc1 == tc2 && length args1 == length args2) $ do
                -- Here, tc1 == tc2 so the arguments must all 
                -- be provably distinct
                guard $ and $ zipWith provablyDistinctTypes args1 args2
          -- In all other cases, there are type vars that are uninhabited
          -- and we therefore cannot conclude anything.
          | otherwise = Nothing
  in isJust res

