module Pass.PartialEval(specByPartialEvaluation) where
import GHC.Plugins
import Control.Monad ( guard, when )
import Data.Maybe ( isJust )
import Utils hiding (prt)
import Engines.Transform (FullTransform(fullTransformM))

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
specByPartialEvaluation :: Opts -> CoreToDo
specByPartialEvaluation opts = CoreDoPluginPass "Specialization by Partial Evaluation" (partialEvalModGuts opts)

prt :: Outputable a => Opts -> a -> CoreM ()
prt opts = prtIf (show_type_eval opts)
prtS :: Opts -> String -> CoreM ()
prtS opts = putMsgSIf (show_type_eval opts)

-- | Performs specialization by partial evaluation on 'ModGuts'
partialEvalModGuts :: Opts -> CorePluginPass
partialEvalModGuts opts mod_guts = do
  prtS opts $ info "Running type-level partial evaluation phase"
  -- First, get all the CoreBinds in the program
  let all_core_binds :: [CoreBind] = mg_binds mod_guts
  all_new_core_binds :: [CoreBind] <- fullTransformM (partialEvalExpr opts) all_core_binds
  -- Once the mod guts have been transformed, return
  return mod_guts { mg_binds = all_new_core_binds }

{- This is the part that actually matters. Here, we are traversing 
 - through an expression in search for the target expression. Once 
 - it is found, we perform partial evaluation based on the rules 
 - presented above. -}
-- | Partially evaluate an 'Expr'.
partialEvalExpr :: Opts
                -> Expr Var -- ^ The expression to evaluate 
                -> CoreM (Expr Var) -- ^ The updated expression after partial 
                                    -- evaluation (if it happened)
{- This is the most interesting case. -}
partialEvalExpr opts expr@(App (App (App (App (App (App (Var f) (Type _)) _) (Type t1)) (Type t2)) _) _)
    | fn_name == target_fn = do
        prtS opts $ info "Target expression found"
        prt opts expr
        -- check if type applications are provably equivalent
        if provablyEquivalentTypes t1 t2 then do
          prtS opts $ info "Type arguments provably equal"
          prtS opts $ success "New expression"
          -- If type applications are provably equivalent, emit True
          let new_expr = mkCoreConApps trueDataCon []
          prt opts new_expr
          return new_expr
        -- check if type applications are provably distinct
        else if provablyDistinctTypes t1 t2 then do
          prtS opts $ info "Type arguments provably equal"
          prtS opts $ success "New expression"
          -- If type applications are provably distinct, emit False
          let new_expr = mkCoreConApps falseDataCon []
          prt opts new_expr
          return new_expr
        else do
          prtS opts $ info "No rewrite"
          -- Don't rewrite
          return expr
  where fn_name = nameStableString $ varName f
        target_fn = "$base$Data.Typeable.Internal$sameTypeRep"
partialEvalExpr _ e = return e

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

