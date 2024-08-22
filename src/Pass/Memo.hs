{-# LANGUAGE PatternSynonyms #-}
module Pass.Memo(memoizedSpecialize) where
import Engines.KnownCase(caseOfKnownCase)
import Engines.Substitution(substitute)
import Engines.LetInline(letInline)
import Engines.BetaReduction
import GHC.Plugins
import Control.Monad
import Data.Maybe 
import GHC.Core.Map.Type
import Engines.DropCasts (DropCasts(dropCasts))
import Engines.LeftElaboration
import Engines.Transform
import Engines.InlineUnfolding (inlineId)


{- This phase should come before all the other optimization phases 
 - in GHC. Therefore, this phase receives, what is effectively, raw 
 - GHC Core that was desugared from Hs code.
 -
 - As a result, we might have completely uninteresting functions like
 -    everything $ f
 - This is a problem because we will then be unable to identify interesting 
 - structures. 
 -
 - As such, prior to this phase there is a simple inlining phase that ensures that 
 - we have some attempt to reveal as much of the desired structure as possible.
 -
 - An alternative is to invoke the simple optimizer, but we will look into that
 - later. 
 -
 - After the simple inlining phase, we should hopefully have some 'nice' structure
 - that we can work with. Particularly, expressions like 
 -     everywhere f
 - should exist in the program, and we shall specialize those.
 -
 - The high-level structure of this phase should be as follows:
 -    1.  Obtain a 'FunctionMap' containing groups of programs that 
 -        have interesting traversals to specialize. The groups are 
 -        specifically "specialization" groups, having precisely
 -        the same implementation, but with different type arguments.
 -        These are grouped together so that we do not emit anything extra.
 -        An alternative is memoization, but determining whether an expression 
 -        is exactly the same might be problematic.
 -    2.  For each specialization group in the 'FunctionMap':
 -        a.  For each traversal in the group:
 -            i.  Emit the smallest function f encapsulating the traversal
 -           ii.  Replace all occurrences of the traversal with f everywhere in the group
 -          iii.  In f, inline the scheme to reveal the static argument transformation of the scheme
 -           iv.  Eliminate the recursive call to the transformed function by replacing it with an 
 -                appropriate invocation to f
 -            v.  Inline the RHS of the transformed function, effectively eliminating the scheme
 -           vi.  Also take note, for each invocation of f, what type arguments and dictionaries
 -                have been passed in so that we can specialize f on those.
 -    3.  For each specializable invocation of f
 -        a.  Specialize f, inlining things like gmapT, emitting SPEC rule
 -        b.  This should potentially reveal a new specialization of f, add this new specializable
 -            invocation to this list 
 -
 - The result *should* be that all specializable occurrences of 'everywhere', 'gmapT' etc have been 
 - eliminated, and should match handwritten code. Later phases will (hopefully) be able to eliminate 
 - invocations of `mkT`-}

-- | The memoized specializing pass specializes traversals.
memoizedSpecialize :: CoreToDo
memoizedSpecialize = CoreDoPluginPass "Memoizing Specialization" memoSpecModGuts

-- | Performs memoizing specialization on the 'ModGuts' of the program
memoSpecModGuts :: CorePluginPass
memoSpecModGuts mod_guts = do
  putMsgS "Running phase: Memoizing Specialization"
  let all_binds    = mg_binds mod_guts
      function_map = initFunctionMap all_binds
  TER { ter_program         = traversal_extracted_program
      , ter_traversal_specs = spec_map
      , ter_traversal_ids   = traversal_ids
      }                                           <- extractTraversals all_binds function_map
  new_program <- goElim traversal_extracted_program traversal_ids
  -- look through spec list for dictionaries that are found in this program
  spec_map' <- inlineDictionaries spec_map new_program
  let swls = map initSpecializationWorkList spec_map'
  (swls', new_program') <- specTraversals swls new_program
  final_pgm <- replaceProgramWithSpecializations new_program' swls'
  let new_mod_guts = mod_guts { mg_binds = final_pgm }
  return new_mod_guts

{- First thing to do: get all functions that have traversals.
 - Some of the functions are actually the same because they are
 - specializations, so we don't want to treat them as separate and 
 - perform the analysis separately. Therefore, we group them 
 - into function groups and extract the traversals for the entire 
 - group.
 -
 - Therefore, the outcome of this is a map of fn -> [fns] 
 - such that the LHS is a function and the RHS is 
 - all the functions with pretty much the same implementation albeit
 - with potentially different specializations. There are several
 - things we might have to take note:
 -    1.  The specializations may not reveal enough to perform our 
 -        specialization. Therefore, we will have to observe if 
 -        the arguments to the traversing combinators are type variables
 -        or not. If there exists one function in this group that 
 -        has a specialization of the combinator, then we will perform
 -        our specialization routine.
 -    2.  Some functions are already "specialized" without a SPECIALIZE 
 -        pragma, for example, the function 
 -            increase :: Float -> Company -> Company
 -            increase k = everywhere $ mkT (incS k)
 -        Although the RHS of 'increase' is actually a generic 
 -        traversal, it has been specialized to 'Company' because 
 -        of the type signature of 'increase'
 - versal @a $dData_
 - As such, the outcome of this first phase is a map 
 -    { fn -> [fns] }
 - where
 -    1.  If the RHS has multiple functions with the same implementation 
 -        but different types, then the LHS function is the unspecialized 
 -        version 
 -    2.  Every function in the RHS has some extractable traversal 
 -    3.  In a list of [fn_names], at least one fn_name has a specialization 
 -        of the traversal. -}

type FunctionMap = [(Id, [Id])]
-- | Initializes the 'FunctionMap' from the program that contains all map entries such that 
--    1.  all RHS functions are equivalent in implementation to
--        the bind location on the LHS
--    2.  in the RHS, at least one of them has a traversal that can be fully-specialized
initFunctionMap :: [CoreBind]  -- ^ The full program
                -> FunctionMap -- ^ The resulting 'FunctionMap'
                          -- get all the specialization groups in the program. these may not 
                          -- be interesting.
initFunctionMap pgm = let specialize_groups           = groupSpecializedFunctions pgm
                          -- get all the interesting functions (ones with specializable traversals)
                          -- 'specialize_groups' is passed in so that we do not duplicate work
                          interesting_fns             = bindsWithTargetExpr specialize_groups pgm
                          -- remove uninteresting specialization groups
                          interesting_specializations = filterSpecializationGroupsWithNoSpecializableTraversal specialize_groups pgm
                          -- result is just the combination of everything interesting
                      in  interesting_fns ++ interesting_specializations


-- | Gets all binds in a program that contain a specialize rule. It produces a 'FunctionMap'
-- id -> [id] such that the LHS id is a bind with rules, and the RHS list of 
-- ids are the specialized versions of the LHS.
groupSpecializedFunctions :: [CoreBind] -- ^ The list of binds in the program
                          -> FunctionMap -- ^ The list of functions with specialization rules
groupSpecializedFunctions [] = []
groupSpecializedFunctions (x : xs) = let names                 = bindersOf x
                                         potential_map_entries = map getSpecializeGroupFromId names
                                         map_entries           = collectNonMaybes potential_map_entries
                                         rec_res               = groupSpecializedFunctions xs
                                     in  map_entries ++ rec_res
  where getSpecializeGroupFromId :: Var -> Maybe (Id, [Id])
        getSpecializeGroupFromId v 
          = do let all_rules_of_bind = idCoreRules v
                   spec_rules_of_bind = filter (isRuleNameSpec . ru_name) all_rules_of_bind
               if null spec_rules_of_bind
               then Nothing
               else do let rhs_of_spec_rules = map ru_rhs spec_rules_of_bind
                           rhs_as_vars = getSpecializedIDsFromSpecExpression rhs_of_spec_rules
                       return (v, v : rhs_as_vars) -- specialization group includes itself
        getSpecializedIDsFromSpecExpression :: [Expr Var] -> [Var]
        getSpecializedIDsFromSpecExpression [] = []
        getSpecializedIDsFromSpecExpression (App f _ : xs') = getSpecializedIDsFromSpecExpression (f : xs')
        getSpecializedIDsFromSpecExpression (Var v : xs') = v : getSpecializedIDsFromSpecExpression xs'
        getSpecializedIDsFromSpecExpression (_ : xs') = getSpecializedIDsFromSpecExpression xs'
        isRuleNameSpec :: RuleName -> Bool
        isRuleNameSpec name = let name_string = show name
                                  header      = drop 1 $ take 5 name_string
                              in  "SPEC" == header
        collectNonMaybes :: [Maybe a] -> [a]
        collectNonMaybes [] = []
        collectNonMaybes (Just x' : xs') = x' : collectNonMaybes xs'
        collectNonMaybes (_ : xs') = collectNonMaybes xs'

-- | Produces a 'FunctionMap' containing the binds that contain the target expression.
bindsWithTargetExpr :: FunctionMap  -- ^ The current map so that duplicates are not added
                    -> [CoreBind]   -- ^ The bind to search
                    -> FunctionMap  -- ^ The a separate 'FunctionMap' containing binds of interest, 
                                    -- excluding those that are specialized
bindsWithTargetExpr mp pgm
    = let flattened_binds = flattenBinds pgm
      in  bux flattened_binds 
  where bux :: [(Id, CoreExpr)] -> FunctionMap
        bux [] = []
        bux ((lhs, rhs) : xs)
          | lhs `elemAnywhere` mp = r
          | containsTargetExpr rhs = (lhs, [lhs]) : r
          | otherwise = r
          where r = bux xs
        
-- | Ensures that every specialization group has at least one specializable traversal.
filterSpecializationGroupsWithNoSpecializableTraversal :: FunctionMap -> [CoreBind] -> FunctionMap
filterSpecializationGroupsWithNoSpecializableTraversal [] _ = []
filterSpecializationGroupsWithNoSpecializableTraversal ((loc, ls_locs) : xs) pgm 
  | any aux ls_locs = (loc, ls_locs) : rec_res
  | otherwise       = rec_res  
  where aux :: Id -> Bool
        aux lhs = let e = lookupTopLevelRHS lhs pgm
                  in  containsTargetExpr e
        rec_res :: FunctionMap
        rec_res = filterSpecializationGroupsWithNoSpecializableTraversal xs pgm

-- | Determines if an expression contains the expression of interest, 
-- e.g. 'everywhere f' or 'everything f q' for some 'f' and 'q'
containsTargetExpr :: Expr Var -> Bool
-- case of everywhere f @t $dt
containsTargetExpr (Everywhere scheme _ type_arg _)
  | isVarEverywhere scheme && isTypeFullyConcrete type_arg = True
-- case of everything @r f q @t $td
containsTargetExpr (Everything scheme _ _ _ t _)
  | isVarEverything scheme && isTypeFullyConcrete t = True
-- case of everywhereM @m $dm f @t $td
containsTargetExpr (EverywhereM scheme _ _ _ t _)
  | isVarEverywhereM scheme && isTypeFullyConcrete t = True
containsTargetExpr (App f arg)           = containsTargetExpr f || containsTargetExpr arg
containsTargetExpr (Var _)               = False
containsTargetExpr (Lit _)               = False
containsTargetExpr (Lam _ e)             = containsTargetExpr e
containsTargetExpr (Let (NonRec _ e') e) = containsTargetExpr e' || containsTargetExpr e
containsTargetExpr (Let (Rec ls) e)      = let es = map snd ls
                                           in any containsTargetExpr (e : es)
containsTargetExpr (Case e _ _ alts)     = let alt_exprs = rhssOfAlts alts 
                                           in any containsTargetExpr (e : alt_exprs)
containsTargetExpr (Cast e _)            = containsTargetExpr e
containsTargetExpr (Tick _ e)            = containsTargetExpr e
containsTargetExpr (Type _)              = False
containsTargetExpr (Coercion _)          = False

elemAnywhere :: Id -> FunctionMap -> Bool
elemAnywhere _ [] = False
elemAnywhere loc ((k, v) : xs) = 
  loc == k || loc `elem` v || loc `elemAnywhere` xs 

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

-- | This function determines if a 'Var' is the 'everywhere' function.
isVarEverywhere :: Var -> Bool
isVarEverywhere v = let name = varName v
                        s    = nameStableString name
                        pre  = take 4 s
                        post = last' (length "$everywhere") s
                    in  pre == "$syb" && (post == "$everywhere" || post == "everywhere'")

-- | This function determines if a 'Var' is the 'everything' function.
isVarEverything :: Var -> Bool
isVarEverything v = let name = varName v
                        s    = nameStableString name
                        pre  = take 4 s
                        post = last' (length "$everything") s
                    in  pre == "$syb" && post == "$everything"

-- | This function determines if a 'Var' is the 'everywhereM' function.
isVarEverywhereM :: Var -> Bool
isVarEverywhereM v = let name = varName v
                         s    = nameStableString name
                         pre  = take 4 s
                         post = last' (length "$everywhereM") s
                     in  pre == "$syb" && post == "$everywhereM"

-- | Drops all the elements in a list except the last few elements.
last' :: Int -> [a] -> [a]
last' x ls | length ls <= x = ls
           | otherwise      = last' x (tail ls)

dropLast :: Int -> [a] -> [a]
dropLast _ [] = []
dropLast n ls@(x : xs)
  | n >= length ls = []
  | otherwise      = x : dropLast n xs

isTypeFullyConcrete :: Type -> Bool
isTypeFullyConcrete t
  | isTyVarTy t = False
  | otherwise   = let res = do
                        (_, args) <- splitTyConApp_maybe t
                        guard $ all isTypeFullyConcrete args
                  in  isJust res

{- Next steps. The idea is to extract out all the traversals so that they can be specialized on their own. 
 - For example, if we have 
 -    increase k x = everywhere (mkT (incS k)) x
 - then we want to extract out specifically 'everywhere (mkT (incS k))' into its own function
 -    traversal k = everywhere (mkT (incS k))
 - and replace the original extracted expression with an invocation of the traversal, i.e. giving
 -    increase k x = traversal k x
 - At this point, we should also maintain a list of specializations for each extracted traversal. 
 - Importantly, we must also keep track of what expressions should be replaced by what. This way, we can 
 - replace the traversals across all specializations in the same specialization group.
 -
 - Therefore, there are several things this pass will do.
 -    1.  Identify a traversal, and make note of type and dictionary arguments on it, if specializable
 -    2.  Emit a new traversal function, and replace it accordingly. Keep track of the substitution performed 
 -        so we may perform the same substitution on it in other functions in the same specialization group
 -
 - Rough algorithm outline:
 -    1.  For each LHS in the FunctionMap:
 -          a. Traverse LHS definition, looking for traversals (BOTTOM UP in case of nested traversals)
 -          b. For each discovered traversal:
 -              i.  Emit traversal
 -             ii.  Store type and dictionary arguments to traversal
 -            iii.  Replace traversal with emitted function
 -             iv.  Store substituted expression -> traversal invocation
 -              v.  Replace substituted expression with traversal invocation in all functions
 -                  in the same specialization group.
 -             vi.  Emit traversal IDs for later inlining and specialization
 - -}

-- | The result of traversal extraction
data TraversalExtractionResult = TER { ter_program          :: CoreProgram
                                     , ter_traversal_specs  :: SpecializationMap
                                     , ter_traversal_ids    :: [Var]
                                     } 

-- | The result of extracting traversals from expressions
data TEExprR = TEER { teer_result_expr        :: Expr Var
                    , teer_spec_map           :: SpecializationMap
                    , teer_subst_map          :: SubstitutionMap
                    , teer_new_binds          :: [CoreBind]
                    , teer_new_traversal_ids  :: [Var]
                    }

-- | Creates an empty 'TEExprR' given an 'Expr Var'
mkEmptyTEExprR :: Expr Var -> TEExprR
mkEmptyTEExprR e = TEER { teer_result_expr        = e
                        , teer_spec_map           = []
                        , teer_subst_map          = []
                        , teer_new_binds          = []
                        , teer_new_traversal_ids  = []
                        }

-- | A 'SpecializationMap' describes the type and dictionary
-- arguments to a traversal. The map is therefore a list 
-- of entries lhs -> rhs such that
--    lhs : ID of a traversal function
--    rhs : list of (type arg, dictionary arg) 
--    type arg is fully concrete
--    dictionary arg is fully accessible and can be moved anywhere
type SpecializationMap = [(Id, [(Type, CoreExpr)])]

-- | A 'SubstitutionMap' specifies what expression should be replaced with
-- what traversal. In each entry, the LHS is an expression that has been
-- extracted over all bound variables of the enclosing bind. I.e.,
-- if we have a definition f = \x.\y. everywhere (mkT x)
-- then the LHS would be \x. everywhere (mkT x). In other words, it is the smallest
-- function enclosing the traversal. 
-- The RHS is then the ID denoting the name of the traversal
type SubstitutionMap = [(CoreExpr, Id)]

-- | A list of bound variables in *reverse order* of occurrence
type BoundVars = [Var]

-- | Extract the traversals in the program into separate functions, and replaces 
-- the traversal expressions with invocations of those functions
extractTraversals :: CoreProgram
                  -> FunctionMap
                  -> CoreM TraversalExtractionResult

-- Nothing to do
extractTraversals program [] = return TER { ter_program         = program
                                          , ter_traversal_specs = []
                                          , ter_traversal_ids   = [] }
-- Main case
extractTraversals program' (fn_map_entry : fn_map) = do
  -- Get any recursive result
  TER { ter_program         = program
      , ter_traversal_specs = traversal_specs
      , ter_traversal_ids   = traversal_ids
      }                                         <- extractTraversals program' fn_map

  -- Now is time to extract the traversals from the current map entry
  let (left_bindloc, right_bindlocs) = fn_map_entry
      left_expr                      = lookupTopLevelRHS left_bindloc program
  -- left_bindloc is the bindlocation on the LHS of the map entry. That bind location 
  -- is a left_var = left_expr. Now we perform the extraction on left_expr
  TEER { teer_result_expr       = left_expr'
       , teer_spec_map          = extracted_spec_map
       , teer_subst_map         = extracted_subst_map
       , teer_new_binds         = extracted_traversal_binds
       , teer_new_traversal_ids = extracted_traversal_ids
       }                                                     <- extractTraversalsFromExpression left_expr []
  
  -- Once the traversals in this bind has been extracted, we update the program.
  -- There are two things to do: 
  --    1.  Add the new binds from the extraction to the program. Add them to the *end*
  --        of the existing program so that bind locations do not get disrupted.
  --    2.  Update left_expr with the newly extracted left_expr'
  let new_program = 
        let program_with_updated_bind = updateBind left_bindloc left_expr' program
        in  program_with_updated_bind ++ extracted_traversal_binds

  -- Given our extracted traversals, it is time to perform the same extraction 
  -- on the functions in the same specialization group.
  (final_program, final_specs) <- pushTraversals new_program 
                                                 right_bindlocs 
                                                 (extracted_spec_map ++ traversal_specs) 
                                                 extracted_subst_map

  -- Combine everything together to form our final result
  return TER { ter_program         = final_program
             , ter_traversal_specs = final_specs
             , ter_traversal_ids   = extracted_traversal_ids ++ traversal_ids }

-- | This pattern matches expressions in the form of `e f @t $d`
pattern Everywhere :: Var -> CoreExpr -> Type -> CoreExpr -> CoreExpr
pattern Everywhere e f t d <- (App (App (App (Var e) f) (Type t)) d)

-- | This pattern matches expressions in the form of `e @t f g @t2 $d`
pattern Everything :: Var -> Type -> CoreExpr -> CoreExpr -> Type -> CoreExpr -> CoreExpr
pattern Everything e t c q qt qd <- App (App (App (App (App (Var e) (Type t)) c) q) (Type qt)) qd

-- | This pattern matches expressions in the form of `e @t $d f @t2 $d2`
pattern EverywhereM :: Var -> Type -> CoreExpr -> CoreExpr -> Type -> CoreExpr -> CoreExpr
pattern EverywhereM e m md tr t d <- App (App (App (App (App (Var e) (Type m)) md) tr) (Type t)) d


-- | Extracts all traversals from an expression. 
extractTraversalsFromExpression :: CoreExpr -> BoundVars -> CoreM TEExprR
{- Important case -}
extractTraversalsFromExpression (Everywhere scheme f' type_arg d_arg) bound_vars
  | isVarEverywhere scheme = do
      -- perform extraction on any other relevant expression
      TEER { teer_result_expr = f
           , teer_spec_map    = specs
           , teer_subst_map   = subst
           , teer_new_binds   = binds
           , teer_new_traversal_ids = ids
           } <- extractTraversalsFromExpression f' bound_vars
      -- the core expression we are abstracting over
      let target_expr = App (Var scheme) f
      extractTraversalsFromTargetExpression target_expr bound_vars type_arg d_arg specs subst binds ids
extractTraversalsFromExpression (Everything s tr c q t d) bound_vars
  | isVarEverything s = do
      -- extract traversals from sub expressions
      rec_result1 <- extractTraversalsFromExpression c bound_vars
      rec_result2 <- extractTraversalsFromExpression q bound_vars
      let real_c = teer_result_expr rec_result1
          real_q  = teer_result_expr rec_result2
          spec   = teer_spec_map rec_result1 ++ teer_spec_map rec_result2
          sub  = teer_subst_map rec_result1 ++ teer_subst_map rec_result2
          binds = teer_new_binds rec_result1 ++ teer_new_binds rec_result2
          ids = teer_new_traversal_ids rec_result1 ++ teer_new_traversal_ids rec_result2
      -- the core expression we are abstracting over
      let target_expr = App (App (App (Var s) (Type tr)) real_c) real_q
      extractTraversalsFromTargetExpression target_expr bound_vars t d spec sub binds ids
extractTraversalsFromExpression (EverywhereM scheme m m_dict f' type_arg d_arg) bound_vars
  | isVarEverywhereM scheme = do
      TEER {
        teer_result_expr = f
        , teer_spec_map = spec
        , teer_subst_map = sub
        , teer_new_binds = binds
        , teer_new_traversal_ids = ids
      } <- extractTraversalsFromExpression f' bound_vars
      -- the core expression we are abstracting over
      let target_expr = App (App (App (Var scheme) (Type m)) m_dict) f
      extractTraversalsFromTargetExpression target_expr bound_vars type_arg d_arg spec sub binds ids
-- Trivial cases
extractTraversalsFromExpression (Var i) _      = return $ mkEmptyTEExprR $ Var i
extractTraversalsFromExpression (Lit l) _      = return $ mkEmptyTEExprR $ Lit l
extractTraversalsFromExpression (Type t) _     = return $ mkEmptyTEExprR $ Type t
extractTraversalsFromExpression (Coercion c) _ = return $ mkEmptyTEExprR $ Coercion c
-- Simple cases
extractTraversalsFromExpression (App f x) bound_vars = do
  TEER { teer_result_expr       = f'
       , teer_spec_map          = spec_map1
       , teer_subst_map         = subst_map1
       , teer_new_binds         = binds1
       , teer_new_traversal_ids = ids1
       }                                      <- extractTraversalsFromExpression f bound_vars
  TEER { teer_result_expr       = x'
       , teer_spec_map          = spec_map2
       , teer_subst_map         = subst_map2
       , teer_new_binds         = binds2
       , teer_new_traversal_ids = ids2
       }                                      <- extractTraversalsFromExpression x bound_vars
  return TEER { teer_result_expr        = App f' x'
              , teer_spec_map           = spec_map1 ++ spec_map2
              , teer_subst_map          = subst_map1 ++ subst_map2
              , teer_new_binds          = binds1 ++ binds2
              , teer_new_traversal_ids  = ids1 ++ ids2 }

extractTraversalsFromExpression (Cast e r) bound_vars = do
  res <- extractTraversalsFromExpression e bound_vars
  let e' = teer_result_expr res
  return res { teer_result_expr = Cast e' r }

extractTraversalsFromExpression (Tick c e) bound_vars = do
  res <- extractTraversalsFromExpression e bound_vars
  let e' = teer_result_expr res
  return res { teer_result_expr = Tick c e' }

-- More important cases
extractTraversalsFromExpression (Lam b e) bound_vars = do
  res <- extractTraversalsFromExpression e (b : bound_vars) -- include 'b' as a bound variable
  let e' = teer_result_expr res
  return res { teer_result_expr = Lam b e' }

extractTraversalsFromExpression (Let b e) bound_vars = do
    let more_vars      = bindersOf b -- let bindings introduce more variables to bind over
        new_bound_vars = more_vars ++ bound_vars
    (b', spec, subst, binds, ids) <- aux b new_bound_vars
    TEER { teer_result_expr       = e'
         , teer_spec_map          = spec'
         , teer_subst_map         = subst'
         , teer_new_binds         = binds'
         , teer_new_traversal_ids = ids'
         }                                  <- extractTraversalsFromExpression e new_bound_vars
    return TEER { teer_result_expr       = Let b' e'
                , teer_spec_map          = spec ++ spec'
                , teer_subst_map         = subst ++ subst'
                , teer_new_binds         = binds ++ binds'
                , teer_new_traversal_ids = ids ++ ids'
                }
  where aux :: Bind Var -> [Var] -> CoreM (Bind Var, SpecializationMap, SubstitutionMap, [CoreBind], [Var])
        aux (NonRec bind_name bind_expr) bvs = do
          TEER { teer_result_expr       = e'
               , teer_spec_map          = spec'
               , teer_subst_map         = subst'
               , teer_new_binds         = binds'
               , teer_new_traversal_ids = ids'
               }                                  <- extractTraversalsFromExpression bind_expr bvs
          return (NonRec bind_name e', spec', subst', binds', ids')
        aux (Rec ls) bvs = do
          (ls', spec', subst', pgm', ids') <- bux ls bvs
          return (Rec ls', spec', subst', pgm', ids')
        bux :: [(Var, Expr Var)] -> [Var] -> CoreM ([(Var, Expr Var)], SpecializationMap, SubstitutionMap, [CoreBind], [Var])
        bux [] _ = return ([], [], [], [], [])
        bux ((lhs, rhs) : xs) bvs = do
          (xs', spec1, subst1, binds1, ids1) <- bux xs bvs
          TEER { teer_result_expr = rhs'
               , teer_spec_map = spec2
               , teer_subst_map = subst2
               , teer_new_binds = binds2
               , teer_new_traversal_ids = ids2
               }                               <- extractTraversalsFromExpression rhs bvs
          return ((lhs, rhs') : xs', spec1 ++ spec2, subst1 ++ subst2, binds1 ++ binds2, ids1 ++ ids2)
extractTraversalsFromExpression (Case e var t alts) bound_vars = do
    TEER { teer_result_expr = e'
         , teer_spec_map = spec1
         , teer_subst_map = subst1
         , teer_new_binds = binds1
         , teer_new_traversal_ids = ids1
         }                                <- extractTraversalsFromExpression e bound_vars
    let new_bound_vars = var : bound_vars
    (alts', spec2, subst2, binds2, ids2) <- aux alts new_bound_vars
    return TEER { teer_result_expr       = Case e' var t alts'
                , teer_spec_map          = spec1 ++ spec2
                , teer_subst_map         = subst1 ++ subst2
                , teer_new_binds         = binds1 ++ binds2
                , teer_new_traversal_ids = ids1 ++ ids2 }
  where aux :: [Alt Var] -> [Var] -> CoreM ([Alt Var], SpecializationMap, SubstitutionMap, [CoreBind], [Var])
        aux [] _ = return ([], [], [], [], [])
        aux (Alt alt_con names expr : xs) bvs = do
          (alts', spec1, subst1, binds1, ids1) <- aux xs bvs
          let new_bound_vars = names ++ bvs
          TEER { teer_result_expr = e'
               , teer_spec_map = spec2
               , teer_subst_map = subst2
               , teer_new_binds = binds2
               , teer_new_traversal_ids = ids2
               }                                <- extractTraversalsFromExpression expr new_bound_vars
          return (Alt alt_con names e' : alts', spec2 ++ spec1, subst2 ++ subst1, binds1 ++ binds2, ids1 ++ ids2)

-- | Extract the traversal from a given target expression
extractTraversalsFromTargetExpression :: CoreExpr -> BoundVars -> Type -> CoreExpr -> SpecializationMap -> SubstitutionMap -> [CoreBind] -> [Id] -> CoreM TEExprR
extractTraversalsFromTargetExpression target_expr bound_vars type_arg dict_arg spec_map subst_map new_binds new_ids 
  = do  -- obtain the occurring bound variables of this expression;
        -- this is so that we can wrap all the bound variables
        -- in lambdas
        let occurring_bound_vars = getOccurringVariables target_expr bound_vars
        -- now we get the type of this expression; we need this so that 
        -- we can create the traversal function type.
        let target_expr_type = exprType target_expr
        -- now we create the type of the traversal function type
        let type_of_traversal = createTraversalFunctionType target_expr_type occurring_bound_vars
        -- now we create the RHS of the traversal; i.e., wrap the core expression around lambdas
        -- of the occuring bound variables. We can also make the substitution template at 
        -- the same time.
        (traversal_rhs, template) <- mkTraversalRHSAndTemplate target_expr occurring_bound_vars type_of_traversal
        -- now make the name of the traversal. we must also give it its type.
        traversal_lhs <- mkTraversalLHS type_of_traversal
        -- now we can make the actual bind. it is for sure recursive, especially once we
        -- eliminate the scheme.
        let new_bind = Rec [(traversal_lhs, traversal_rhs)]
        -- now the original expression needs to be replaced with an invocation
        -- of the newly created traversal function.
        let replaced_expr = createReplacedTraversal traversal_lhs type_arg dict_arg occurring_bound_vars
        -- we also need to register the template and resulting id to replace with,
        -- in the substitution map
        let subst_entry = (template, traversal_lhs)
        -- if these arguments are specializable, add them to the specialization map
        let specs = if isTypeFullyConcrete type_arg && null (getOccurringVariables dict_arg bound_vars)
                    then pushEntryToMapOfList traversal_lhs (type_arg, dict_arg) spec_map
                    else spec_map
        return $ TEER { teer_result_expr = replaced_expr
                      , teer_spec_map    = specs
                      , teer_subst_map   = subst_entry : subst_map
                      , teer_new_binds = new_bind : new_binds
                      , teer_new_traversal_ids = traversal_lhs : new_ids }

-- | Pushes a k -> v pair into a map of k -> [v]
pushEntryToMapOfList :: Eq k => k -> v -> [(k, [v])] -> [(k, [v])]
pushEntryToMapOfList k v [] = [(k, [v])]
pushEntryToMapOfList k v ((lhs, rhs) : entries)
  | k == lhs = (lhs, rhs) : entries
  | otherwise = (lhs, rhs) : pushEntryToMapOfList k v entries

pushTraversals :: CoreProgram 
               -> [Id] 
               -> SpecializationMap 
               -> SubstitutionMap 
               -> CoreM (CoreProgram, SpecializationMap)
pushTraversals pgm [] spec_map _ = return (pgm, spec_map)
pushTraversals pgm' (id' : ids) spec_map' subst_map = do
  (pgm, spec_map) <- pushTraversals pgm' ids spec_map' subst_map
  let rhs = lookupTopLevelRHS id' pgm
  (rhs', specs) <- pushTraversalsIntoExpression rhs subst_map []
  let new_pgm = updateBind id' rhs' pgm
  return (new_pgm, specs ++ spec_map)

createTraversalFunctionType :: Type -- ^ type of everywhere f
                            -> BoundVars -- ^ list of bound variables
                            -> Type -- ^ type of traversal
createTraversalFunctionType target_expr_type bound_vars = 
    let (forall_, rhs) = splitForAllTyVars target_expr_type
        (_many, data_arg, a_to_a)      = splitFunTy rhs
        fn_type = aux a_to_a bound_vars
        with_data = mkVisFunTy Many data_arg fn_type
        full_type = mkSpecForAllTys forall_ with_data
    in full_type
  where aux :: Type -> [Var] -> Type
        aux acc [] = acc
        aux acc (v : vs)
          | isTyVar v = let fn_type = mkSpecForAllTy v acc
                        in  aux fn_type vs
          | otherwise = let fn_type = mkVisFunTy Many (exprType (Var v)) acc
                        in aux fn_type vs
        -- aux acc (v : vs) = let fn_type = mkVisFunTy Many (exprType (Var v)) acc
        --                    in  aux fn_type vs


performSubstitution :: Expr Var -> (Expr Var, Var) -> CoreM (Maybe Var)
performSubstitution candidate (matcher, traversal) = do
  if deBruijnize candidate == deBruijnize matcher then 
    return $ return traversal
  else 
    return Nothing

tryAllSubstitutions :: Expr Var -> SubstitutionMap -> CoreM (Maybe Var)
tryAllSubstitutions _ [] = return Nothing
tryAllSubstitutions candidate (x : xs) = do
  x' <- performSubstitution candidate x
  case x' of 
    Nothing -> tryAllSubstitutions candidate xs
    y -> return y


pushTraversalsIntoExpression :: Expr Var -> SubstitutionMap -> [Var] -> CoreM (Expr Var, SpecializationMap)
pushTraversalsIntoExpression (App (App (App (Var combinator) transformation) (Type arg_to_combinator)) dictionary_arg_to_combinator) subst_map bound_vars
  | isVarEverywhere combinator = do
      -- perform push on any other relevant expression
      (real_transformation, spec1) <- pushTraversalsIntoExpression transformation subst_map bound_vars
      let target_expr = App (Var combinator) real_transformation
      let bound_vars_of_expression = getOccurringVariables real_transformation bound_vars
      let type_of_target_expr = exprType target_expr
      let type_of_traversal = createTraversalFunctionType type_of_target_expr bound_vars_of_expression
      (_, template_left) <- mkTraversalRHSAndTemplate target_expr bound_vars_of_expression type_of_traversal
      mTraversal <- tryAllSubstitutions template_left subst_map
      case mTraversal of 
        Just traversal ->
          -- create the new expression
          let replacement = createReplacedTraversal traversal arg_to_combinator dictionary_arg_to_combinator bound_vars_of_expression
              new_spec = if isTypeFullyConcrete arg_to_combinator && null (getOccurringVariables dictionary_arg_to_combinator bound_vars) then pushEntryToMapOfList traversal (arg_to_combinator, dictionary_arg_to_combinator) spec1 else spec1
          in return (replacement, new_spec)
              
        Nothing -> let actual_expr = App (App (App (Var combinator) real_transformation) (Type arg_to_combinator)) dictionary_arg_to_combinator
                   in return (actual_expr, spec1)
-- pushTraversalsIntoExpression (App (App (App (Var combinator) transformation) (Type arg_to_combinator)) dictionary_arg_to_combinator) subst_map bound_vars
pushTraversalsIntoExpression (Everything combinator tr c q t d) subst_map bound_vars
  | isVarEverything combinator = do
      -- perform push on any other relevant expression
      (real_c, spec_c) <- pushTraversalsIntoExpression c subst_map bound_vars
      (real_q, spec_q) <- pushTraversalsIntoExpression q subst_map bound_vars
      let spec1 = spec_c ++ spec_q
      let target_expr = App (App (App (Var combinator) (Type tr)) real_c) real_q
      -- (real_transformation, spec1) <- pushTraversalsIntoExpression transformation subst_map bound_vars
      -- let target_expr = App (Var combinator) real_transformation
      let bound_vars_of_expression = getOccurringVariables target_expr bound_vars
      let type_of_target_expr = exprType target_expr
      let type_of_traversal = createTraversalFunctionType type_of_target_expr bound_vars_of_expression
      (_, template_left) <- mkTraversalRHSAndTemplate target_expr bound_vars_of_expression type_of_traversal
      -- prt template_left
      mTraversal <- tryAllSubstitutions template_left subst_map
      case mTraversal of 
        Just traversal ->
          -- create the new expression
          let replacement = createReplacedTraversal traversal t d bound_vars_of_expression
              new_spec = if isTypeFullyConcrete t && null (getOccurringVariables d bound_vars) then pushEntryToMapOfList traversal (t, d) spec1 else spec1
          in return (replacement, new_spec)
              
        Nothing -> let actual_expr = App (App (target_expr) (Type t)) d
                   in return (actual_expr, spec1)
pushTraversalsIntoExpression (EverywhereM combinator tr c q t d) subst_map bound_vars
  | isVarEverything combinator = do
      -- perform push on any other relevant expression
      (real_c, spec_c) <- pushTraversalsIntoExpression c subst_map bound_vars
      (real_q, spec_q) <- pushTraversalsIntoExpression q subst_map bound_vars
      let spec1 = spec_c ++ spec_q
      let target_expr = App (App (App (Var combinator) (Type tr)) real_c) real_q
      -- (real_transformation, spec1) <- pushTraversalsIntoExpression transformation subst_map bound_vars
      -- let target_expr = App (Var combinator) real_transformation
      let bound_vars_of_expression = getOccurringVariables target_expr bound_vars
      let type_of_target_expr = exprType target_expr
      let type_of_traversal = createTraversalFunctionType type_of_target_expr bound_vars_of_expression
      (_, template_left) <- mkTraversalRHSAndTemplate target_expr bound_vars_of_expression type_of_traversal
      -- prt template_left
      mTraversal <- tryAllSubstitutions template_left subst_map
      case mTraversal of 
        Just traversal ->
          -- create the new expression
          let replacement = createReplacedTraversal traversal t d bound_vars_of_expression
              new_spec = if isTypeFullyConcrete t && null (getOccurringVariables d bound_vars) then pushEntryToMapOfList traversal (t, d) spec1 else spec1
          in return (replacement, new_spec)
              
        Nothing -> let actual_expr = App (App (target_expr) (Type t)) d
                   in return (actual_expr, spec1)
pushTraversalsIntoExpression (Var i) _ _ = return (Var i, [])
pushTraversalsIntoExpression (Lit l) _ _ = return (Lit l, [])
pushTraversalsIntoExpression (Type t) _ _ = return (Type t, [])
pushTraversalsIntoExpression (Coercion c) _ _ = return (Coercion c, [])
{- Simple cases -}
pushTraversalsIntoExpression (App f x) subst_map bound_vars = do
  (f', spec_map1) <- pushTraversalsIntoExpression f subst_map bound_vars
  (x', spec_map2) <- pushTraversalsIntoExpression x subst_map bound_vars
  return (App f' x', spec_map1 ++ spec_map2)
pushTraversalsIntoExpression (Cast e r) subst_map bound_vars = do
  (e', spec) <- pushTraversalsIntoExpression e subst_map bound_vars
  return (Cast e' r, spec)
pushTraversalsIntoExpression (Tick c e) subst_map bound_vars = do
  (e', spec) <- pushTraversalsIntoExpression e subst_map bound_vars
  return (Tick c e', spec)
{- More important cases -}
pushTraversalsIntoExpression (Lam b e) subst_map bound_vars = do
  (e', spec) <- pushTraversalsIntoExpression e subst_map (b : bound_vars) -- include the binder b in the bound variables
  return (Lam b e', spec)
pushTraversalsIntoExpression (Let b e) subst_map bound_vars = do
    let more_vars = binders b -- let bindings introduce more variables to bind over
        new_bound_vars = more_vars ++ bound_vars
    (b', spec) <- aux b new_bound_vars
    (e', spec') <- pushTraversalsIntoExpression e subst_map new_bound_vars
    return (Let b' e', spec ++ spec')
  where aux :: Bind Var -> [Var] -> CoreM (Bind Var, SpecializationMap)
        aux (NonRec bind_name bind_expr) bvs = do
          (e', spec') <- pushTraversalsIntoExpression bind_expr subst_map bvs
          return (NonRec bind_name e', spec')
        aux (Rec ls) bvs = do
          (ls', spec') <- bux ls bvs
          return (Rec ls', spec')
        bux :: [(Var, Expr Var)] -> [Var] -> CoreM ([(Var, Expr Var)], SpecializationMap)
        bux [] _ = return ([], [])
        bux ((lhs, rhs) : xs) bvs = do
          (res1, res2) <- bux xs bvs
          (res4, res5) <- pushTraversalsIntoExpression rhs subst_map bvs
          return ((lhs, res4) : res1, res5 ++ res2)
        binders :: Bind Var -> [Var]
        binders (NonRec lhs _) = [lhs]
        binders (Rec ls) = map fst ls
pushTraversalsIntoExpression (Case e var t alts) subst_map bound_vars = do
    (e', spec1) <- pushTraversalsIntoExpression e subst_map bound_vars
    let new_bound_vars = var : bound_vars
    (alts', spec2) <- aux alts new_bound_vars
    return (Case e' var t alts', spec1 ++ spec2)
  where aux :: [Alt Var] -> [Var] -> CoreM ([Alt Var], SpecializationMap)
        aux [] _ = return ([], [])
        aux (Alt alt_con names expr : xs) bvs = do
          (alts', spec1) <- aux xs bvs
          let new_bound_vars = names ++ bvs
          (e', spec2) <- pushTraversalsIntoExpression expr subst_map new_bound_vars
          return (Alt alt_con names e' : alts', spec2 ++ spec1)


abstractExpressionOverBoundVariables :: Expr Var -> [Var] -> Expr Var
abstractExpressionOverBoundVariables = foldl (flip Lam)

mkUniqTypeVar :: String -> CoreM TyVar
mkUniqTypeVar name = do
  uniq <- getUniqueM
  let name' = mkInternalName uniq (mkVarOcc name) (UnhelpfulSpan UnhelpfulGenerated)
  return $ mkTyVar name' liftedTypeKind

mkTraversalRHSAndTemplate :: Expr Var -> [Var] -> Type -> CoreM (Expr Var, Expr Var)
mkTraversalRHSAndTemplate inner_expr bs t = do
    let (original_type_variable, rhs) = splitForAllTyVars t 
        (_many, data_arg, inner_type) = splitFunTy rhs
    -- create the type variable
    ty_var_var <- mkUniqTypeVar "a"
    let type_variable = mkTyVarTy ty_var_var
    -- create the dict variable
    let (data_tycon,_) = splitAppTy data_arg 
    let data_arg_type = mkAppTy data_tycon type_variable
    data_arg_name <- do
      uniq <- getUniqueM
      let name = mkInternalName uniq (mkVarOcc "$dData") (UnhelpfulSpan UnhelpfulGenerated)
      return $ mkLocalVar VanillaId name Many data_arg_type vanillaIdInfo
    -- apply the inner expression with the type and dict variable
    let inner_expr_with_type_and_dict_apps :: Expr Var = App (App inner_expr (Type type_variable)) (Var data_arg_name)
    -- wrap bs around lambdas over the inner expression
    let expr_abstracted_over_bvs :: Expr Var = abstractExpressionOverBoundVariables inner_expr_with_type_and_dict_apps bs
    expr_renamed <- bux expr_abstracted_over_bvs bs
    -- wrap dict variable as lambda over that expression
    let with_dict_abst :: Expr Var = Lam data_arg_name expr_renamed
    -- wrap type variable as lambda over that expression
    let full_rhs :: Expr Var = Lam ty_var_var with_dict_abst
    -- template generation
    let template = abstractExpressionOverBoundVariables inner_expr bs
    -- perform a full substitution so that uniqueness of variables is preserved
    return (full_rhs, template)
  where bux :: Expr Var -> [Var] -> CoreM (Expr Var)
        bux e [] = return e
        bux e (v : vs) = do
          v' <- mkDerivedUniqueName v
          let e' = substitute v v' e
          bux e' vs

-- | Handy function for deriving a new unique var from an 
-- original var with the same details
mkDerivedUniqueName :: Var -> CoreM Var
mkDerivedUniqueName v = do uniq1 <- getUniqueM
                           uniq2 <- getUniqueM
                           uniq3 <- getUniqueM
                           let new_name = let original = varName v
                                              local_occ = mkLocalOcc uniq1
                                          in  mkDerivedInternalName local_occ
                                                                    uniq2
                                                                    original
                           return $ setVarName (setVarUnique v uniq3) new_name

mkTraversalLHS :: Type -> CoreM Var
mkTraversalLHS t = do
  uniq1 <- getUniqueM 
  uniq2 <- getUniqueM
  let name = mkInternalName uniq1 (mkLocalOcc uniq2 (mkVarOcc "traversal")) (UnhelpfulSpan UnhelpfulGenerated)
  return $ mkLocalId name Many t

createReplacedTraversal :: Id -> Type -> CoreExpr -> BoundVars -> CoreExpr
createReplacedTraversal traversal_name type_arg dict_arg = aux base_expr
  where base_expr :: Expr Var 
        base_expr = App (App (Var traversal_name) (Type type_arg)) dict_arg
        aux e [] = e
        aux e (b : bs)
          | isTyVar b = let e' = aux e bs in App e' (Type $ mkTyVarTy b)
          | otherwise = let e' = aux e bs in App e' (Var b)

orderPreservingIntersection :: Eq a => [a] -> [a] -> [a]
orderPreservingIntersection _ [] = []
orderPreservingIntersection x (y : ys) = if y `elem` x
                                         then y : (x `orderPreservingIntersection` ys)
                                         else x `orderPreservingIntersection` ys
                                        

getOccurringVariables :: Expr Var -> [Var] -> [Var]
getOccurringVariables (Var v) bvs = filter ( == v) bvs
getOccurringVariables (Lit _) _ = []
getOccurringVariables (App f x) bvs = (getOccurringVariables f bvs ++ getOccurringVariables x bvs) `orderPreservingIntersection` bvs
getOccurringVariables (Lam _ e) bvs = getOccurringVariables e bvs
getOccurringVariables (Let b e) bvs = (aux b ++ getOccurringVariables e bvs) `orderPreservingIntersection` bvs
  where aux :: Bind Var -> [Var]
        aux (NonRec _ e') = getOccurringVariables e' bvs
        aux (Rec ls) = bux ls
        bux :: [(Var, Expr Var)] -> [Var]
        bux [] = []
        bux ((_, e'): xs) = (getOccurringVariables e' bvs ++ bux xs) `orderPreservingIntersection` bvs
getOccurringVariables (Case e _ _ alts) bvs = (getOccurringVariables e bvs ++ aux alts) `orderPreservingIntersection` bvs
  where aux :: [Alt Var] -> [Var]
        aux [] = []
        aux (Alt _ _ e' : xs) = (getOccurringVariables e' bvs ++ aux xs) `orderPreservingIntersection` bvs 
getOccurringVariables (Cast e _) bvs = getOccurringVariables e bvs
getOccurringVariables (Tick _ e) bvs = getOccurringVariables e bvs
getOccurringVariables (Type t) bvs 
  | isTyVarTy t = filter ( == (getTyVar "how can this be!?" t)) bvs
  | isForAllTy t = let (_, x) = splitForAllTyVars t
                   in getOccurringVariables (Type x) bvs
  | isFunTy t = let (_, t1, t2) = splitFunTy t
                in (getOccurringVariables (Type t1) bvs ++ getOccurringVariables (Type t2) bvs) `orderPreservingIntersection` bvs
  | Just (_, ty_apps) <- splitTyConApp_maybe t
    = foldr f [] ty_apps

  | otherwise = let (t1, t2) = splitAppTy t
                in (getOccurringVariables (Type t1) bvs ++ getOccurringVariables (Type t2) bvs) `orderPreservingIntersection` bvs
 where f t ls = (getOccurringVariables (Type t) bvs ++ ls) `orderPreservingIntersection` bvs
getOccurringVariables (Coercion _) _ = []

updateBind :: Id -> CoreExpr -> CoreProgram -> CoreProgram
updateBind id' _ [] = pprPanic "cannot look for bind!" (ppr id')
updateBind id' rhs (NonRec b e : binds)
  | id' == b = NonRec b rhs : binds
  | otherwise = NonRec b e : updateBind id' rhs binds
updateBind id' rhs (Rec ls : binds) 
  | id' `elem` map fst ls = Rec (aux ls) : binds
  | otherwise = Rec ls : updateBind id' rhs binds
  where aux :: [(Id, CoreExpr)] -> [(Id, CoreExpr)]
        aux [] = pprPanic "cannot look for bind!" (ppr id')
        aux ((lhs, rhs') : xs) 
          | lhs == id' = (lhs, rhs) : xs
          | otherwise  = (lhs, rhs') : aux xs

{- Next step: Go elimination. 
 -
 - The idea is incredibly simple. Given a traversal:
 -    traversal @a $b c d = everywhere (f ...)
 -
 - Inline everywhere
 -    traversal @a $b c d = (\x -> let rec { go = x . (gmapT go) } in go) (f ...)
 -
 - replace RHS go in binding
 -    traversal @a $b c d = (\x -> let rec { go = x . (gmapT (traversal @a $b c d)) } in go) (f ...)
 -
 - evaluate the lambda
 -    traversal @a $b c d = let rec { go = x . (gmapT (traversal @a $b c d)) } in go
 -
 - inline go
 -    traversal @a $b c d = x . (gmapT (traversal @a $b c d))
 -
 - Algorithm overview:
 -    For each traversal_id f:
 -        1.  Lookup RHS of f
 -        2.  Traverse into main traversal function, keeping track of all the lambda bound variables
 -        3.  Main traversal function is in the form of everywhere x @t $d
 -        4.  Obtain unfolding of everywhere
 -        5.  Replace everywhere with unfolding 
 -        6.  Within unfolding, find the let rec bind LHS and RHS
 -        7.  Replace letrec bind RHS occurrence of letrec bind LHS with invocation of f 
 -        8.  Eval the fully evaluate the application of (\y ...) x @t $d
 -        9.  Inline all occurrences of letrec bind LHS with its RHS
 -  -}

-- | Intelligently optimizes the structure of traversals in a way that makes them
-- amenable for optimization.
goElim :: CoreProgram -- ^ The program
       -> [Id] -- ^ The IDs of the traversal functions
       -> CoreM CoreProgram -- ^ The resulting program
goElim pgm [] = return pgm
goElim pgm' (x : xs) = do
  pgm <- goElim pgm' xs
  let rhs = lookupTopLevelRHS x pgm
  rhs' <- goElimTraversal x rhs
  -- let bindLoc = lookupBindNameForSure pgm x 
  let pgm'' = updateBind x rhs' pgm
  return pgm''

goElimTraversal :: Id -> CoreExpr -> CoreM CoreExpr
goElimTraversal lhs rhs = do
  -- descend into the actual everywhere function
  let traversal_structure = destructureTraversal rhs []
  let scheme = ts_scheme traversal_structure
  let everywhere_unfolding = unfoldingTemplate $ realIdUnfolding scheme
  -- prt everywhere_unfolding
  let inlined_unfolding = letInline everywhere_unfolding
  go_replacement <- mkGoReplacement lhs traversal_structure
  let unfolding_with_replaced_go = pushGoReplacementIntoInlinedUnfolding inlined_unfolding go_replacement
  let let_inlined_unfolding_with_replaced_go = letInline unfolding_with_replaced_go
  -- let beta_reduced_let_inlined_go = betaReduceCompletely let_inlined_unfolding_with_replaced_go deBruijnize
  beta_reduced_let_inlined_go <- betaReduceCompletelyM let_inlined_unfolding_with_replaced_go
  let rhs' = substitute scheme beta_reduced_let_inlined_go rhs
  -- let rhs'' = betaReduceCompletely rhs' deBruijnize
  betaReduceCompletelyM rhs' 
  

class NameShow a where
  showAllNames :: a -> CoreM ()


instance NameShow CoreExpr where
  showAllNames :: CoreExpr -> CoreM ()
  showAllNames (Var v) = putMsgS $ nameStableString $ varName v
  showAllNames (Lit id) = return ()
  showAllNames (App f x) = do showAllNames f; showAllNames x
  showAllNames (Lam _ rhs) = showAllNames rhs
  showAllNames (Let lhs rhs) = do showAllNames lhs; showAllNames rhs
  showAllNames (Case e' b t alts) = do showAllNames e'; showAllNames alts
  showAllNames (Cast e c) = showAllNames e
  showAllNames (Tick _ e) = showAllNames e
  showAllNames e = return ()
instance NameShow a => NameShow [a] where
  showAllNames = mapM_ showAllNames
instance NameShow CoreBind where
  showAllNames (NonRec _ rhs) = showAllNames rhs
  showAllNames (Rec ls) = showAllNames ls
instance NameShow (Id, CoreExpr) where
  showAllNames (_, e) = showAllNames e
instance NameShow (Alt Var) where
  showAllNames (Alt _ _ e) = showAllNames e
class TypeShow a where
  showAllTypes :: a -> CoreM ()

prt :: Outputable a => a -> CoreM()
prt = putMsg . ppr

instance TypeShow CoreExpr where
  showAllTypes :: CoreExpr -> CoreM ()
  showAllTypes (Type _) = return ()
  showAllTypes (Var v)
    | isTyVar v = return ()
    | otherwise = do putMsgS $ nameStableString $ varName v
                     prt $ exprType $ Var v
  showAllTypes e@(App f x) = do showAllTypes f
                                showAllTypes x
                                prt e
                                prt $ exprType e
  showAllTypes e@(Lam _ rhs) = do showAllTypes rhs
                                  -- showAllTypes b
                                  prt e
                                  prt $ exprType e
  showAllTypes e@(Let lhs rhs) = do showAllTypes lhs
                                    showAllTypes rhs
                                    prt e
                                    prt $ exprType e
  showAllTypes e@(Case e' b t alts) = do showAllTypes e'
                                         -- showAllTypes b
                                         mapM_ showAllTypes alts
                                         prt e
                                         prt $ exprType e
  showAllTypes e@(Cast e' _) = do showAllTypes e'
                                  prt e
                                  prt $ exprType e
  showAllTypes e@(Tick _ e') = do showAllTypes e'
                                  prt e
                                  prt $ exprType e
  showAllTypes e = do putMsg $ ppr e
                      putMsg $ ppr $ exprType e

instance TypeShow CoreBind where
  showAllTypes (NonRec _ rhs) = showAllTypes rhs
  showAllTypes (Rec ls) = mapM_ showAllTypes ls
instance TypeShow (Id, CoreExpr) where
  showAllTypes (_, e) = showAllTypes e
instance TypeShow (Alt Var) where
  showAllTypes (Alt _ _ e) = showAllTypes e
mkGoReplacement :: Id -> TraversalStructure -> CoreM CoreExpr
mkGoReplacement traversal_name traversal_structure = do
  let bound_vars = ts_bvs traversal_structure
      type_param = last bound_vars
      dict_arg = ts_dict_arg traversal_structure
      dict_param_type = exprType dict_arg
  new_type_param <- mkUniqTypeVar "t1"
  new_dict_param <- do
      uniq <- getUniqueM
      let name = mkInternalName uniq (mkVarOcc "$dData_internal_") (UnhelpfulSpan UnhelpfulGenerated)
      let var = mkLocalVar VanillaId name Many dict_param_type vanillaIdInfo
      return $ substitute type_param new_type_param var
  let new_bound_vars = substitute type_param new_type_param $ dropLast 2 bound_vars
  let lambda_body = createReplacedTraversal traversal_name (mkTyVarTy new_type_param) (Var new_dict_param) new_bound_vars
  return $ Lam new_type_param (Lam new_dict_param lambda_body) 

pushGoReplacementIntoInlinedUnfolding :: CoreExpr -> CoreExpr -> CoreExpr 
pushGoReplacementIntoInlinedUnfolding (Let (Rec ((lhs, rhs) : [])) e) go_replacement = 
  let new_rhs = substitute lhs go_replacement rhs
  in  Let (NonRec lhs new_rhs) e
pushGoReplacementIntoInlinedUnfolding (App f x) b = App (pushGoReplacementIntoInlinedUnfolding f b)
                                                        (pushGoReplacementIntoInlinedUnfolding x b)
pushGoReplacementIntoInlinedUnfolding (Lam b e) r = Lam b (pushGoReplacementIntoInlinedUnfolding e r)
pushGoReplacementIntoInlinedUnfolding v _ = v

inlineDictionaries :: SpecializationMap -> CoreProgram -> CoreM SpecializationMap
inlineDictionaries spec_map pgm = fullTransformM (inlineDictionariesExpr pgm) spec_map
-- inlineDictionariesEntry :: CoreProgram -> (Id, [(Type, CoreExpr)]) -> (Id, [(Type, CoreExpr)])
-- inlineDictionariesEntry pgm (id, (t, e)) = (id, inlineDictionariesExpr pgm)
inlineDictionariesExpr :: CoreProgram -> CoreExpr -> CoreM CoreExpr
inlineDictionariesExpr pgm (Var v)
  = do let lhss = pgm >>= bindersOf
       if v `elem` lhss
       then do putMsgS "FOUND INLINABLE DICTIONARY"
               prt v
               return $ lookupTopLevelRHS v pgm 
       else return $ Var v
inlineDictionariesExpr _ e = return e

data TraversalStructure = TS { ts_scheme :: Id
                             , ts_type_arg :: Type
                             , ts_dict_arg :: CoreExpr
                             , ts_bvs :: BoundVars
                             , ts_transform :: CoreExpr }

destructureTraversal :: CoreExpr -> BoundVars -> TraversalStructure
destructureTraversal (Everywhere scheme transformation type_arg dict_arg) bvs
  | isVarEverywhere scheme
  = TS { ts_scheme = scheme
     , ts_type_arg = type_arg
     , ts_dict_arg = dict_arg
     , ts_transform = transformation
     , ts_bvs = bvs }
destructureTraversal (Everything scheme tc c q t d) bvs 
  | isVarEverything scheme
    = TS { ts_scheme = scheme
    , ts_type_arg = t
    , ts_dict_arg = d
    , ts_transform = q
    , ts_bvs = bvs }
destructureTraversal (EverywhereM scheme monad monad_dict transformation t d) bvs
  | isVarEverywhereM scheme
    = TS { ts_scheme = scheme
    , ts_type_arg = t
    , ts_dict_arg = d
    ,ts_transform = transformation
    , ts_bvs = bvs }
destructureTraversal (Lam b e) bvs = destructureTraversal e (b : bvs)
destructureTraversal _ _ = panic "the impossible happened! the traversal has a different structure than originally intended"

data SpecializationWorklist = SWL { swl_traversal_id :: Id
                                  , swl_worklist :: [(Type, CoreExpr)]
                                  , swl_completed :: [(Type, Id)] }

-- | creating the SWL
initSpecializationWorkList :: (Id, [(Type, CoreExpr)]) -> SpecializationWorklist
initSpecializationWorkList (id', ls) = SWL { swl_traversal_id = id'
                                          , swl_worklist = ls
                                          , swl_completed = []}

specTraversals :: [SpecializationWorklist] -> CoreProgram -> CoreM ([SpecializationWorklist], CoreProgram)
specTraversals [] pgm = return ([], pgm)
specTraversals (swl : swls) pgm = do
  (swl', pgm') <- specTraversal swl pgm
  (swls', pgm'') <- specTraversals swls pgm'
  return (swl' : swls', pgm'')

specTraversal :: SpecializationWorklist -> CoreProgram -> CoreM (SpecializationWorklist, CoreProgram)
specTraversal sw@(SWL { swl_worklist = [] }) pgm = return (sw, pgm)
specTraversal sw@(SWL { swl_completed = ls }) pgm
  | length ls > 30 = return (sw, pgm)
specTraversal sw pgm = do
  let SWL { swl_traversal_id = t_id 
          , swl_worklist     = worklist'
          , swl_completed    = completed } = sw
      ((type_arg, dict_arg) : worklist) = worklist' -- earlier case handled the empty worklist
  if isSpecCompleted type_arg completed then
    -- already specialized, ignore and move to next workitem
    specTraversal (sw { swl_worklist = worklist }) pgm else
    -- perform the traversal
    do (specialized_id, specialized_id_rhs, new_work) <- specOneTraversal t_id type_arg dict_arg pgm
       let new_completed = (type_arg, specialized_id) : completed
       let added_worklist = new_work ++ worklist
       let new_pgm = NonRec specialized_id specialized_id_rhs : pgm
       specTraversal sw { swl_worklist = added_worklist, swl_completed = new_completed } new_pgm 

  -- return (sw, pgm)

specOneTraversal :: Id -> Type -> CoreExpr -> CoreProgram -> CoreM (Id, CoreExpr, [(Type, CoreExpr)])
specOneTraversal t_id type_arg dict_arg pgm = do
  -- obtain the RHS of the traversal ID to specialize
  let traversal_rhs = lookupTopLevelRHS t_id pgm
  -- let specialized_rhs = betaReduceCompletely (App (App traversal_rhs (Type type_arg)) dict_arg) deBruijnize
  specialized_rhs <- betaReduceCompletelyM (App (App traversal_rhs (Type type_arg)) dict_arg)
  specialized_id <- mkDerivedUniqueName t_id
  (final_rhs, new_specs) <- optimizeSpecialization t_id specialized_rhs 
  let final_spec_id = setIdType specialized_id (exprType final_rhs)
  return (final_spec_id, final_rhs, new_specs)

isSpecCompleted :: Type -> [(Type, Id)] -> Bool
isSpecCompleted t ls = let types = map fst ls
                           db_types = map deBruijnize types
                       in deBruijnize t `elem` db_types

optimizeSpecialization :: Id -> CoreExpr -> CoreM (CoreExpr, [(Type, CoreExpr)])
optimizeSpecialization gen_traversal_id spec_rhs = do
  -- prt spec_rhs
  -- rhs' <- genericElimination spec_rhs
  rhs' <- fullTransformM gmapTEliminator spec_rhs --transform gmapTDestructurer gmapTTransformer spec_rhs
  -- let rhs = betaReduceCompletely rhs' deBruijnize
  rhs <- betaReduceCompletelyM (letInline rhs')
  prt rhs
  let specs = getSpecializations gen_traversal_id [] rhs
  -- prt specs
  return (rhs, specs)

gmapTEliminator :: CoreExpr -> CoreM CoreExpr
gmapTEliminator (App (App (Var v) (Type t)) d)
  | nameStableString (varName v) == "$base$Data.Data$gmapT"
    = do
          let uf = unfoldingTemplate $ realIdUnfolding v
          d' <- leftInlineLikeCrazy d
          x <- betaReduceCompletelyM (App (App uf (Type t)) d')
          let type_specific_gmapT = caseOfKnownCase x
          tttt <- leftInlineLikeCrazy type_specific_gmapT
          let tttttttt'' = letInline tttt
          actual_gmapT <- betaReduceCompletelyM tttttttt''
          return actual_gmapT
gmapTEliminator (App (App (Var v) (Type t)) d)
  | nameStableString (varName v) == "$base$Data.Data$gmapQ"
    = do
          -- putMsgS "UNFOLDING"
          let uf = unfoldingTemplate $ realIdUnfolding v
          -- prt uf
          d' <- leftInlineLikeCrazy d
          -- putMsgS "DICTIONARY"
          -- prt d'
          -- putMsgS "BETA REDUCING"
          -- let x = betaReduceCompletely' (App (App uf (Type t)) d') deBruijnize
          x <- betaReduceCompletelyM (App (App uf (Type t)) d')
          -- prt x
          -- putMsgS "CASE OF KNOWN CASE"
          let x' = caseOfKnownCase x
          -- prt x'
          -- putMsgS "DROP CASTS"
          let y = x' -- dropCasts x'
          -- prt y
          let type_specific_gmapT = y
          -- putMsgS "ACTUAL GMAPQ"
          -- prt type_specific_gmapT
          -- putMsgS "UNFOLDING ACTUAL GMAPT"
          tttt <- leftInlineLikeCrazy type_specific_gmapT
          -- putMsgS "INLINED"
          -- prt tttt
          return tttt
          -- putMsgS "DROP CASTS"
          -- let tttttt = dropCasts tttt
          -- prt tttttt
          -- putMsgS "UNFOLDING GUNFOLD IN CASE"
          -- tttttttt' <- leftInlineLikeCrazy tttttt
          -- prt tttttttt'
          -- putMsgS "Let-Inlining"
          -- let tttttttt'' = letInline tttttttt'
          -- prt tttttttt''
          -- putMsgS "Beta Reduction"
          -- xxx123 <- betaReduceCompletelyM tttttttt''
          -- prt xxx123
          -- putMsgS "DROP CASTS"
          -- let actual_gmapT = dropCasts $ xxx123
          -- prt actual_gmapT
          -- return actual_gmapT
gmapTEliminator (App (App (App (App (Var v) (Type t)) d) (Type t2)) d2)
  | nameStableString (varName v) == "$base$Data.Data$gmapM"
    = do
          -- putMsgS "UNFOLDING"
          let uf = unfoldingTemplate $ realIdUnfolding v
          -- prt uf
          d' <- leftInlineLikeCrazy d
          -- putMsgS "DICTIONARY"
          -- prt d'
          -- putMsgS "BETA REDUCING"
          x <- betaReduceCompletelyM (App (App uf (Type t)) d')
          -- prt x
          -- putMsgS "CASE OF KNOWN CASE"
          let x' = caseOfKnownCase x
          -- prt x'
          -- putMsgS "DROP CASTS"
          let y = x' -- dropCasts x'
          -- prt y
          let type_specific_gmapT = y
          -- putMsgS "ACTUAL GMAPM"
          -- prt type_specific_gmapT
          -- putMsgS "UNFOLDING ACTUAL GMAPT"
          tttt <- leftInlineLikeCrazy type_specific_gmapT
          -- prt tttt
          return $ App (App tttt (Type t2)) d2
          -- putMsgS "DICTIONARY FOR MONAD"
          -- d2' <- leftInlineLikeCrazy d2
          -- prt d2'
          -- putMsgS "BETA REDUCE DICT MONAD"
          -- d3 <- betaReduceCompletelyM d2'
          -- prt d3
          -- let fullTypeSpecificGmapM = App (App (tttt) (Type t2)) d2
          -- putMsgS "FULL"
          -- prt fullTypeSpecificGmapM
          -- d3' <- betaReduceCompletelyM fullTypeSpecificGmapM
          -- let d3''' = caseOfKnownCase d3'
          -- putMsgS "Case of known case and beta reduction"
          -- prt d3'''
          -- -- return tttt
          -- return (App (App (App (App (Var v) (Type t)) d) (Type t2)) d2)
          -- return (App (App (Var v) (Type t)) d)
          -- putMsgS "UNFOLDING ACTUAL GMAPT"
          -- tttt <- leftInlineLikeCrazy type_specific_gmapT
          -- prt tttt
          -- return tttt
          -- ------- 
          -- putMsgS "DROP CASTS"
          -- let tttttt = dropCasts tttt
          -- prt tttttt
          -- putMsgS "UNFOLDING GUNFOLD IN CASE"
          -- tttttttt' <- leftInlineLikeCrazy tttttt
          -- prt tttttttt'
          -- putMsgS "Let-Inlining"
          -- let tttttttt'' = letInline tttttttt'
          -- prt tttttttt''
          -- putMsgS "Beta Reduction"
          -- xxx123 <- betaReduceCompletelyM tttttttt''
          -- prt xxx123
          -- putMsgS "DROP CASTS"
          -- let actual_gmapT = dropCasts $ xxx123
          -- prt actual_gmapT
          -- return actual_gmapT
gmapTEliminator x = return x

leftInlineLikeCrazy :: CoreExpr -> CoreM CoreExpr
leftInlineLikeCrazy = leftElaborationLikeCrazy extractor inlineId (betaReduceCompletely)
  where extractor :: CoreExpr -> Maybe Id
        extractor (Var v) = Just v
        extractor _       = Nothing

class GetSpecializations a where
  getSpecializations :: Id -> [Var] -> a -> [(Type, CoreExpr)]

instance GetSpecializations CoreExpr where 
  getSpecializations :: Id -> [Var] -> CoreExpr -> [(Type, CoreExpr)]
  getSpecializations gen_traversal_id bvs (App (App (Var v) (Type t)) d) 
    | v == gen_traversal_id && null (getOccurringVariables d bvs) = 
        (t, d) : (getSpecializations gen_traversal_id bvs d)
  getSpecializations gen_traversal_id bvs (App f x) = (getSpecializations gen_traversal_id bvs f) ++
                                                          (getSpecializations gen_traversal_id bvs x)
  getSpecializations gen_traversal_id bvs (Lam b e) = getSpecializations gen_traversal_id (b : bvs) e
  getSpecializations gen_traversal_id bvs (Let b e) = let bdrs = bindersOf b
                                                          new_bvs = bdrs ++ bvs
                                                      in (getSpecializations gen_traversal_id new_bvs b) ++
                                                          (getSpecializations gen_traversal_id new_bvs e) 
  getSpecializations gen_traversal_id bvs (Case e b t alts) = getSpecializations gen_traversal_id bvs e ++
                                                                getSpecializations gen_traversal_id (b : bvs) alts
  getSpecializations gen_traversal_id bvs (Cast e c) = getSpecializations gen_traversal_id bvs e
  getSpecializations gen_traversal_id bvs (Tick c e) = getSpecializations gen_traversal_id bvs e
  getSpecializations _ _ _ = []

instance GetSpecializations (Alt Var) where
  getSpecializations gen_traversal_id bvs (Alt alt_con bs e) = getSpecializations gen_traversal_id (bs ++ bvs) e


instance GetSpecializations a => GetSpecializations [a] where
  getSpecializations g b ls = ls >>= getSpecializations g b

instance GetSpecializations CoreBind where
  getSpecializations gen_traversal_id bvs (NonRec b e) = getSpecializations gen_traversal_id (b : bvs) e
  getSpecializations gen_traversal_id bvs (Rec ls) = getSpecializations gen_traversal_id (bindersOf (Rec ls) ++ bvs) ls

instance GetSpecializations(Id, CoreExpr) where
  getSpecializations gen_traversal_id bvs (var, e) = getSpecializations gen_traversal_id (var : bvs) e

replaceProgramWithSpecializations :: CoreProgram -> [SpecializationWorklist] -> CoreM CoreProgram
replaceProgramWithSpecializations pgm swls = do
  let ls = map (\x -> (swl_traversal_id x, swl_completed x)) swls
  replaceProgramWithSpecs pgm ls


replaceProgramWithSpecs :: CoreProgram -> [(Id, [(Type, Id)])] -> CoreM CoreProgram
replaceProgramWithSpecs pgm [] = return pgm
replaceProgramWithSpecs pgm' ((lhs, specs) : ls) = do
  pgm <- replaceProgramWithSpecs pgm' ls
  pgm2 <- replaceWithSpecializations lhs specs pgm
  return pgm2

  
replaceExprWithSpec' :: Id -> [(Type, Id)] -> CoreExpr -> CoreM CoreExpr
replaceExprWithSpec' lhs specs (App (App (Var i) (Type t)) _)
  | i == lhs && any (\(x, _) -> deBruijnize x == deBruijnize t) specs = do
      -- get the actual spec
      let Just new_id = lookup (deBruijnize t) (map (\(x, y) -> (deBruijnize x, y)) specs)
      return $ Var new_id 
replaceExprWithSpec' _ _ x = return x

replaceWithSpecializations :: FullTransform CoreExpr b => Id -> [(Type, Id)] -> b -> CoreM b
replaceWithSpecializations id' specs = fullTransformM (replaceExprWithSpec' id' specs)
