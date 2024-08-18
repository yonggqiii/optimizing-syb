{-# LANGUAGE PatternSynonyms #-}
module Pass.Memo(memoizedSpecialize) where
import Engines.KnownCase(caseOfKnownCase)
import Engines.Substitution(substitute)
import Engines.LetInline(letInline)
import Engines.BetaReduction
import GHC.Plugins
import Control.Applicative
import Control.Monad
import Data.Maybe 
import GHC.Core.Map.Type
import Engines.DropCasts (DropCasts(dropCasts))
import GHC.IO (unsafePerformIO)
import Engines.Transform


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
  putMsgS "== Phase: Memoizing Specialization =="
  let all_binds    :: [CoreBind]  = mg_binds mod_guts
      function_map :: FunctionMap = initFunctionMap all_binds
  TER { ter_program = traversal_extracted_program
      , ter_traversal_specs = spec_map
      , ter_traversal_ids = traversal_ids
      }                                           <- extractTraversals all_binds function_map
  new_program <- goElim traversal_extracted_program traversal_ids
  let swls = map initSpecializationWorkList spec_map
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

-- -- | A 'BindLocation' describes the location of a 'CoreBind' within a 
-- -- 'CoreProgram'
-- data BindLocation = TopLevelLocation -- ^ The location of a non-recursive 'CoreBind' or a recursive group
--                       Int -- ^ The index of the 'CoreProgram' this top-level find occurs in
--                   | RecLocation -- ^ The location of a bind within a recursive group
--                       Int -- ^ The index of the 'CoreProgram' the recursive group is located
--                       Int -- ^ The index of the bind pair within the recursive group
--   deriving (Show, Eq)

type FunctionMap = [(Id, [Id])]

-- | Gets all binds in a program that contain a specialize rule. It produces a 'FunctionMap'
-- loc -> [locs] such that the LHS location is a bind with rules, and the RHS list of 
-- locations are the specialized versions of the LHS.
groupSpecializedFunctions :: [CoreBind] -- ^ The list of binds in the program
                          -> FunctionMap -- ^ The list of functions with specialization rules
groupSpecializedFunctions pgm = aux pgm
        -- 'aux' traverses the program, finding specialization groups
  where aux :: [CoreBind] -> FunctionMap
        -- boring
        aux [] = []
        -- non recursive binding case
        aux ((NonRec name _) : xs) = 
              -- look for specializations in this binding
          let potential_map_entry = bux name
              -- recursively search the rest of the program
              r = aux xs
          in case potential_map_entry of
                -- something came up in this binding
                Just map_entry -> map_entry : r
                -- nothing came up, just give recursive result
                Nothing -> r
        -- recursive group case
        aux (Rec ls : xs) =
              -- get all the names in the recursive group
          let names_in_rec_group = map fst ls
              -- look through each binding in the recursive group
              potential_map_entries = map bux names_in_rec_group
              -- obtain only the entries
              map_entries = collectNonMaybes potential_map_entries
              -- get the recursive result for the rest of the program
              r = aux xs
              -- collect them together
          in  map_entries ++ r

        -- bux looks for a recursive group in a single variable
        bux :: Var -> Maybe (Id, [Id])
        bux v = do
              -- get all the rules in this bind
          let all_rules_of_bind = idCoreRules v
              -- only get the specialize (SPEC) rules in this bind
              spec_rules_of_bind = filter (isRuleNameSpec . ru_name) all_rules_of_bind
          if null spec_rules_of_bind then
            -- no specialize rules, don't bother
            Nothing
          else do
                -- get the RHS expressions from the rules
            let rhs_of_spec_rules  = map ru_rhs spec_rules_of_bind
                -- get those expressions as vars
                rhs_as_vars        = getVarsFromExpressions rhs_of_spec_rules
            return (v, v : rhs_as_vars)
            --     -- get the vars as bind locations
            --     rhs_as_bind_locs   = collectNonMaybes $ map (lookupBindName pgm) rhs_as_vars
            --     -- get the LHS var as a bind location
            --     lhs_bind_loc  = lookupBindNameForSure pgm v
            --     -- create the map entry; RHS contains itself
            --     map_entry          = (lhs_bind_loc, lhs_bind_loc : rhs_as_bind_locs)
            -- return map_entry

-- | Produces a 'FunctionMap' containing the binds that contain the target expression.
bindsWithTargetExpr :: FunctionMap  -- ^ The current map so that duplicates are not added
                    -> [CoreBind]   -- ^ The bind to search
                    -> FunctionMap  -- ^ The a separate 'FunctionMap' containing binds of interest, 
                                    -- excluding those that are specialized
bindsWithTargetExpr mp pgm = aux pgm
        -- aux traverses the program and actually searches for binds that contain the
        -- target expression
  where aux :: [CoreBind] -> FunctionMap 
        -- base case is uninteresting
        aux [] = []
        -- Non-recursive bind case
        aux (NonRec b e : xs) 
            -- If the bind b is already part of the existing 'FunctionMap', don't bother
            | b `elemAnywhere` mp = rec_res
            -- If the RHS contains the target expression, add that to the resulting 'FunctionMap'
            | containsTargetExpr e    = (b, [b]) : rec_res
            -- If none of the above, don't bother with this entry either
            | otherwise               = rec_res
                
          where -- 'rec_res' is the recursive result of 'aux' applied to the remainder of the
                -- program, 'xs'
                rec_res = aux xs
        -- Recursive group: search for binds among the group with the target expression, and the 
        -- binds in the remainder of the program, and add them together
        aux (Rec ls : xs) = bux ls ++ aux xs

        -- 'bux' traverses a list of bind pairs and searches for binds in that list that 
        -- contain the target expression
        bux :: [(Var, Expr Var)] -> FunctionMap
        -- base case is uninteresting
        bux [] = []
        -- traverse the list of binds in the recursive group
        bux ((b, e) : bs)
            | b `elemAnywhere` mp = rec_res
            | containsTargetExpr e    = (b, [b]) : rec_res
            | otherwise               = rec_res
          where rec_res = bux bs

        
{- As it turns out, the target expression looks something like 
 - $ @LiftedRep @(forall a. Data a => a -> a) @(forall a. Data a => a -> a) everywhere (mkT ...) ... 
 - Thus in determining whether a bind is relevant, we should just look for every single identifier 
 - and look for the 'everywhere' function.
 - Furthermore, we cannot rely on the name stable string entirely, because 
 - it includes the hash of the library, possibly determining versions.
 - As such, because it looks something like syb.....$everywhere, that is what we should check for.
 -
 - Also, it is not the case that the target expression looks like the above. It could actually 
 - be in the form of everywhere (mkT ...) ... 
 -
 - We will probably need a more sophisticated form of expression checking that handles these two cases.
 - -}

-- | Ensures that every specialization group has at least one specializable traversal.
filterSpecializationGroupsWithNoSpecializableTraversal :: FunctionMap -> [CoreBind] -> FunctionMap
filterSpecializationGroupsWithNoSpecializableTraversal [] _ = []
filterSpecializationGroupsWithNoSpecializableTraversal ((loc, ls_locs) : xs) pgm 
  | any aux ls_locs = (loc, ls_locs) : rec_res
  | otherwise       = rec_res  
  where aux :: Id -> Bool
        aux lhs = let e = lookupTopLevelRHS lhs pgm
                  in  containsTargetExpr e
                  --     res = do e <- lookupTopLevelRHS lhs pgm
                  --              guard $ containsTargetExpr e
                  -- in  isJust res
        rec_res :: FunctionMap
        rec_res = filterSpecializationGroupsWithNoSpecializableTraversal xs pgm

-- | Determines if an expression contains the expression of interest, 
-- i.e. 'everywhere f' for some 'f'
containsTargetExpr :: Expr Var -> Bool
-- case of everywhere f @Type $dict
containsTargetExpr (Everywhere combinator transformation arg_to_combinator dict_arg)
  | isVarEverywhere combinator && isTypeFullyConcrete arg_to_combinator = True
  | otherwise                                                           = containsTargetExpr transformation || containsTargetExpr dict_arg
containsTargetExpr (App f arg)           = containsTargetExpr f || containsTargetExpr arg
containsTargetExpr (Var _)               = False
containsTargetExpr (Lit _)               = False
containsTargetExpr (Lam _ e)             = containsTargetExpr e
containsTargetExpr (Let (NonRec _ e') e) = containsTargetExpr e' || containsTargetExpr e
containsTargetExpr (Let (Rec ls) e)      = let es = map snd ls
                                           in any containsTargetExpr (e : es)
containsTargetExpr (Case e _ _ alts)     = let alt_exprs = map aux alts 
                                           in any containsTargetExpr (e : alt_exprs)
  where aux :: Alt b -> Expr b 
        aux (Alt _ _ e') = e'
containsTargetExpr (Cast e _)            = containsTargetExpr e
containsTargetExpr (Tick _ e)            = containsTargetExpr e
containsTargetExpr (Type _)              = False
containsTargetExpr (Coercion _)          = False

pushEntryToMapOfList :: Eq k => k -> v -> [(k, [v])] -> [(k, [v])]
pushEntryToMapOfList k v [] = [(k, [v])]
pushEntryToMapOfList k v ((lhs, rhs) : entries)
  | k == lhs = (lhs, rhs) : entries
  | otherwise = (lhs, rhs) : pushEntryToMapOfList k v entries


isRuleNameSpec :: RuleName -> Bool
isRuleNameSpec name = let name_string = show name
                          header      = drop 1 $ take 5 name_string
                      in  "SPEC" == header

getVarsFromExpressions :: [Expr Var] -> [Var]
getVarsFromExpressions [] = []
getVarsFromExpressions (Var v : xs) = v : getVarsFromExpressions xs
getVarsFromExpressions (_ : xs) = getVarsFromExpressions xs

collectNonMaybes :: [Maybe a] -> [a]
collectNonMaybes [] = []
collectNonMaybes (Just x : xs) = x : collectNonMaybes xs
collectNonMaybes (_ : xs) = collectNonMaybes xs

elemAnywhere :: Id -> FunctionMap -> Bool
elemAnywhere _ [] = False
elemAnywhere loc ((k, v) : xs) = 
  loc == k || loc `elem` v || loc `elemAnywhere` xs 

lookupTopLevelRHS_maybe :: Id -> [CoreBind] -> Maybe CoreExpr
lookupTopLevelRHS_maybe _ [] = Nothing
lookupTopLevelRHS_maybe id' (NonRec lhs rhs : bs)
  | id' == lhs = Just rhs
  | otherwise = lookupTopLevelRHS_maybe id' bs
lookupTopLevelRHS_maybe id' (Rec ls : bs) =
    case aux ls of 
      Nothing -> lookupTopLevelRHS_maybe id' bs
      x -> x
  where aux :: [(Id, CoreExpr)] -> Maybe CoreExpr
        aux [] = Nothing
        aux ((lhs, rhs) : rs)
          | id' == lhs = Just rhs
          | otherwise = aux rs

lookupTopLevelRHS :: Id -> [CoreBind] -> CoreExpr
lookupTopLevelRHS id' pgm = case lookupTopLevelRHS_maybe id' pgm of
  Just x -> x
  Nothing -> panic "the impossible happened... cannot find RHS of bind"

-- | This function determines if a 'Var' is the 'everywhere' function.
isVarEverywhere :: Var -> Bool
isVarEverywhere v = let name = varName v
                        s    = nameStableString name
                        pre  = take 4 s
                        post = last' (length "$everywhere") s
                    in  pre == "$syb" && post == "$everywhere"

-- | Determines if a 'Var' is the '($)' function
isVarDollar :: Var -> Bool
isVarDollar v = let name = varName v
                    s    = nameStableString name
                in  s == "$base$GHC.Base$$"
-- | Drops all the elements in a list except the last few elements.
last' :: Int -> [a] -> [a]
last' x ls | length ls <= x = ls
           | otherwise      = last' x (tail ls)

dropLast :: Int -> [a] -> [a]
dropLast n [] = []
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

-- | Extracts all traversals from an expression. 
extractTraversalsFromExpression :: CoreExpr -> BoundVars -> CoreM TEExprR
{- Important case -}
extractTraversalsFromExpression (Everywhere combinator transformation arg_to_combinator dictionary_arg_to_combinator) bound_vars
  | isVarEverywhere combinator = do
      -- perform extraction on any other relevant expression
      rec_result <- extractTraversalsFromExpression transformation bound_vars 
      let real_transformation = teer_result_expr rec_result
          spec1               = teer_spec_map rec_result
          subst1              = teer_subst_map rec_result
          core_binds1         = teer_new_binds rec_result
          new_traversal_ids   = teer_new_traversal_ids rec_result

      let target_expr = App (Var combinator) real_transformation
      -- obtain the bound variables of this expression
      let bound_vars_of_expression = getOccurringVariables real_transformation bound_vars
      let type_of_target_expr = exprType target_expr
      let type_of_traversal = createTraversalFunctionType type_of_target_expr bound_vars_of_expression
      -- create the RHS
      (traversal_rhs, template_left) <- mkTraversalRHSAndTemplate target_expr bound_vars_of_expression type_of_traversal
      traversal_lhs <- mkTraversalLHS type_of_traversal
      let new_bind_for_traversal = Rec [(traversal_lhs, traversal_rhs)]
      -- create the replaced traversal
      let replaced_expr = createReplacedTraversal traversal_lhs arg_to_combinator dictionary_arg_to_combinator bound_vars_of_expression
      let template_entry = (template_left, traversal_lhs)
      -- check if specializable
      new_spec <- 
        if isTypeFullyConcrete arg_to_combinator && null (getOccurringVariables dictionary_arg_to_combinator bound_vars) then do
          putMsgS " ==== PUSH ==== "
          prt arg_to_combinator
          prt dictionary_arg_to_combinator
          return $ pushEntryToMapOfList traversal_lhs (arg_to_combinator, dictionary_arg_to_combinator) spec1
        else do
          putMsgS " ==== NO PUSH ==== "
          prt arg_to_combinator
          prt dictionary_arg_to_combinator
          return spec1 
        
      -- putMsg $ ppr new_bind_for_traversal
      -- putMsg $ ppr replaced_expr
      return TEER { teer_result_expr        = replaced_expr
                  , teer_spec_map           = new_spec
                  , teer_subst_map          = template_entry : subst1
                  , teer_new_binds          = new_bind_for_traversal : core_binds1
                  , teer_new_traversal_ids  = traversal_lhs : new_traversal_ids}
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
        aux acc (v : vs) = let fn_type = mkVisFunTy Many (exprType (Var v)) acc
                           in  aux fn_type vs


performSubstitution :: Expr Var -> (Expr Var, Var) -> CoreM (Maybe Var)
performSubstitution candidate (matcher, traversal) = do
  -- putMsgS "======= COMPARISONS ==============="
  -- putMsg $ ppr candidate
  -- putMsg $ ppr matcher
  if deBruijnize candidate == deBruijnize matcher then 
    return $ return traversal
  else 
    return Nothing

tryAllSubstitutions :: Expr Var -> SubstitutionMap -> CoreM (Maybe Var)
tryAllSubstitutions candidate [] = return Nothing
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
  return $ mkExportedVanillaId name t

createReplacedTraversal :: Id -> Type -> CoreExpr -> BoundVars -> CoreExpr
createReplacedTraversal traversal_name type_arg dict_arg = aux base_expr
  where base_expr :: Expr Var 
        base_expr = App (App (Var traversal_name) (Type type_arg)) dict_arg
        aux e [] = e
        aux e (b : bs) = let e' = aux e bs
                         in  App e' (Var b)


getOccurringVariables :: Expr Var -> [Var] -> [Var]
getOccurringVariables (Var v) bvs = filter ( == v) bvs
getOccurringVariables (Lit _) _ = []
getOccurringVariables (App f x) bvs = getOccurringVariables f bvs ++ getOccurringVariables x bvs
getOccurringVariables (Lam _ e) bvs = getOccurringVariables e bvs
getOccurringVariables (Let b e) bvs = aux b ++ getOccurringVariables e bvs
  where aux :: Bind Var -> [Var]
        aux (NonRec _ e') = getOccurringVariables e' bvs
        aux (Rec ls) = bux ls
        bux :: [(Var, Expr Var)] -> [Var]
        bux [] = []
        bux ((_, e'): xs) = getOccurringVariables e' bvs ++ bux xs
getOccurringVariables (Case e _ _ alts) bvs = getOccurringVariables e bvs ++ aux alts
  where aux :: [Alt Var] -> [Var]
        aux [] = []
        aux (Alt _ _ e' : xs) = getOccurringVariables e' bvs ++ aux xs
getOccurringVariables (Cast e _) bvs = getOccurringVariables e bvs
getOccurringVariables (Tick _ e) bvs = getOccurringVariables e bvs
getOccurringVariables (Type _) _ = []
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
  let inlined_unfolding = letInline everywhere_unfolding
  go_replacement <- mkGoReplacement lhs traversal_structure
  let unfolding_with_replaced_go = pushGoReplacementIntoInlinedUnfolding inlined_unfolding go_replacement
  let let_inlined_unfolding_with_replaced_go = letInline unfolding_with_replaced_go
  let beta_reduced_let_inlined_go = betaReduceCompletely let_inlined_unfolding_with_replaced_go deBruijnize
  let rhs' = substitute scheme beta_reduced_let_inlined_go rhs
  let rhs'' = betaReduceCompletely rhs' deBruijnize
  -- showAllTypes rhs''
  return rhs''

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


data TraversalStructure = TS { ts_scheme :: Id
                             , ts_type_arg :: Type
                             , ts_dict_arg :: CoreExpr
                             , ts_bvs :: BoundVars
                             , ts_transform :: CoreExpr }

destructureTraversal :: CoreExpr -> BoundVars -> TraversalStructure
destructureTraversal (Everywhere scheme transformation type_arg dict_arg) bvs =
  TS { ts_scheme = scheme
     , ts_type_arg = type_arg
     , ts_dict_arg = dict_arg
     , ts_transform = transformation
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
  let specialized_rhs = betaReduceCompletely (App (App traversal_rhs (Type type_arg)) dict_arg) deBruijnize
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
  -- rhs' <- genericElimination spec_rhs
  rhs' <- transform gmapTDestructurer gmapTTransformer spec_rhs
  let rhs = betaReduceCompletely rhs' deBruijnize
  prt rhs
  let specs = getSpecializations gen_traversal_id [] rhs
  -- prt specs
  return (rhs, specs)

gmapTDestructurer :: CoreExpr -> Maybe (Id, Type, CoreExpr)
gmapTDestructurer (App (App (Var v) (Type t)) d)
  | nameStableString (varName v) == "$base$Data.Data$gmapT"
    = return (v, t, d)
gmapTDestructurer _ = Nothing

gmapTTransformer :: (Id, Type, CoreExpr) -> CoreM CoreExpr
gmapTTransformer (v, t, d) = do
      let uf = unfoldingTemplate $ realIdUnfolding v
      d' <- fullyElaborateDFunUnfoldingsLikeCrazy d
      --putMsgS%%%"DICTIONARY"
      --prt%%%d'
      --putMsgS%%%"BETA REDUCING"
      let x = betaReduceCompletely (App (App uf (Type t)) d') deBruijnize
      --prt%%%x
      --putMsgS%%%"CASE OF KNOWN CASE"
      let x' = caseOfKnownCase x
      --prt%%%x'
      --putMsgS%%%"DROP CASTS"
      let y = dropCasts x'
      --prt%%%y
      let type_specific_gmapT = y
      --prt%%%type_specific_gmapT
      --putMsgS%%%"UNFOLDING ACTUAL GMAPT"
      tttt <- fullyElaborateDFunUnfoldingsLikeCrazy type_specific_gmapT
      --prt%%%tttt
      -- let (Var v') = type_specific_gmapT
      -- --prt%%%$ exprType (Var v')
      -- --prt%%%$ unfoldingTemplate $ realIdUnfolding v
      --putMsgS%%%"DROP CASTS"
      let tttttt = dropCasts tttt
      --prt%%%tttttt
      --putMsgS%%%"UNFOLDING GUNFOLD IN CASE"
      tttttttt' <- fullyElaborateLHS tttttt
      --prt%%%tttttttt'
      --putMsgS%%%"Let-Inlining"
      let tttttttt'' = letInline tttttttt'
      --prt%%%tttttttt''
      --putMsgS%%%"Beta Reduction"
      let xxx123 = betaReduceCompletely tttttttt'' deBruijnize
      --prt%%%xxx123
      --putMsgS%%%"DROP CASTS"
      let actual_gmapT = dropCasts $ xxx123
      --prt%%%actual_gmapT

      return actual_gmapT



-- TODO: make this proper
genericElimination :: CoreExpr -> CoreM CoreExpr
genericElimination (App (App (Var v) (Type t)) d)
  | nameStableString (varName v) == "$base$Data.Data$gmapT" = do
      --putMsgS%%%"FOUND"
      --prt%%%v
      let uf = unfoldingTemplate $ realIdUnfolding v
      d' <- fullyElaborateDFunUnfoldingsLikeCrazy d
      --putMsgS%%%"DICTIONARY"
      --prt%%%d'
      --putMsgS%%%"BETA REDUCING"
      let x = betaReduceCompletely (App (App uf (Type t)) d') deBruijnize
      --prt%%%x
      --putMsgS%%%"CASE OF KNOWN CASE"
      let x' = caseOfKnownCase x
      --prt%%%x'
      --putMsgS%%%"DROP CASTS"
      let y = dropCasts x'
      --prt%%%y
      let type_specific_gmapT = y
      --prt%%%type_specific_gmapT
      --putMsgS%%%"UNFOLDING ACTUAL GMAPT"
      tttt <- fullyElaborateDFunUnfoldingsLikeCrazy type_specific_gmapT
      --prt%%%tttt
      -- let (Var v') = type_specific_gmapT
      -- --prt%%%$ exprType (Var v')
      -- --prt%%%$ unfoldingTemplate $ realIdUnfolding v
      --putMsgS%%%"DROP CASTS"
      let tttttt = dropCasts tttt
      --prt%%%tttttt
      --putMsgS%%%"UNFOLDING GUNFOLD IN CASE"
      tttttttt' <- fullyElaborateLHS tttttt
      --prt%%%tttttttt'
      --putMsgS%%%"Let-Inlining"
      let tttttttt'' = letInline tttttttt'
      --prt%%%tttttttt''
      --putMsgS%%%"Beta Reduction"
      let xxx123 = betaReduceCompletely tttttttt'' deBruijnize
      --prt%%%xxx123
      --putMsgS%%%"DROP CASTS"
      let actual_gmapT = dropCasts $ xxx123
      --prt%%%actual_gmapT

      return actual_gmapT
    
-- genericElimination (Var v)
--   | nameStableString (varName v) == "$base$Data.Data$gmapT" = do
--       --putMsgS%%%"FOUND"
--       --prt%%%v
--       let uf = unfoldingTemplate $ realIdUnfolding v
--       return uf
--   | otherwise = return (Var v)
genericElimination (Lam b e) = 
  do e' <- genericElimination e
     return $ Lam b e'
genericElimination (App f x) =
  do f' <- genericElimination f
     x' <- genericElimination x
     return (App f' x')
genericElimination (Let b e) = do
  e' <- genericElimination e
  return $ Let b e'
genericElimination (Case e b t alts) = do
  e' <- genericElimination e
  return $ Case e' b t alts
genericElimination (Cast e c) = do 
  e' <- genericElimination e
  return $ Cast e' c
genericElimination (Tick c e) = do
  e' <- genericElimination e
  return $ Tick c e'
genericElimination x = return x

fullyElaborateDFunUnfoldingsLikeCrazy :: CoreExpr -> CoreM CoreExpr
fullyElaborateDFunUnfoldingsLikeCrazy x = do
  -- x' <- fullyElaborateDFunUnfoldings x
  x' <- fullyElaborateLHS x
  if deBruijnize x == deBruijnize x' then
      return x
  else 
      fullyElaborateDFunUnfoldingsLikeCrazy x'

-- TODO: handle more complex DFuns
fullyElaborateDFunUnfoldings :: CoreExpr -> CoreM CoreExpr
fullyElaborateDFunUnfoldings (Var v) = do
  let uf = realIdUnfolding v
  case uf of 
    DFunUnfolding bndrs df_con df_args -> do
      -- --prt%%%bndrs
      -- --prt%%%df_con
      -- --prt%%%$ dataConRepType df_con
      -- --prt%%%df_args
      let dfune = mkCoreConApps df_con df_args
      let dfun = foldr Lam dfune bndrs
      --putMsgS%%%"=== GENERATED DFUN ==="
      --prt%%% dfun
      return  dfun
    CoreUnfolding tmpl _ _ _ _ -> do
      return tmpl
    OtherCon s -> do
      --putMsgS%%%"=== OTHERCON ==="
      --prt%%%v
      return $ Var v
    NoUnfolding -> do
      --putMsgS%%%"=== NO UNFOLDING ==="
      --prt%%%v
      return $ Var v

    _ -> do
      --putMsgS%%%"=== NO UNFOLDING!? ==="
      --prt%%%v
      return $ Var v
  -- --prt%%%uf
  -- --putMsgS%%%" ==== above is unfolding term. lets see the template ===="
  -- --prt%%%$ unfoldingTemplate uf
  -- return $ Var v
fullyElaborateDFunUnfoldings (App f x) = do
  f' <- fullyElaborateDFunUnfoldings f
  let res = betaReduceCompletely (App f' x) deBruijnize
  return $ res
fullyElaborateDFunUnfoldings x = return x

fullyElaborateLHS :: CoreExpr -> CoreM CoreExpr
fullyElaborateLHS (Var v) = fullyElaborateDFunUnfoldings (Var v)
fullyElaborateLHS (Lam b e) = do e' <- fullyElaborateLHS e
                                 return $ Lam b e'
fullyElaborateLHS (App f x) = do f' <- fullyElaborateLHS f
                                 return $ betaReduceCompletely (App f' x) deBruijnize
fullyElaborateLHS x = return x

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
  pgm2 <- replaceProgramWithSpec lhs specs pgm
  return pgm2

replaceProgramWithSpec :: Id -> [(Type, Id)] -> CoreProgram -> CoreM CoreProgram
replaceProgramWithSpec _ _ [] = return []
replaceProgramWithSpec lhs specs (x : xs) = do
  xs' <- replaceProgramWithSpec lhs specs xs
  x' <- replaceBindWithSpec lhs specs x
  return $ x' : xs'

replaceBindWithSpec :: Id -> [(Type, Id)] -> CoreBind -> CoreM CoreBind
replaceBindWithSpec lhs specs (NonRec b e) = do
  e' <- replaceExprWithSpec lhs specs e
  return $ NonRec b e'
replaceBindWithSpec lhs specs (Rec ls) = do
  ls' <- mapM (replacePairsWithSpec lhs specs) ls
  return $ Rec ls'

replacePairsWithSpec :: Id -> [(Type, Id)] -> (Id, CoreExpr) -> CoreM (Id, CoreExpr)
replacePairsWithSpec lhs specs (i, e) = do
  e' <- replaceExprWithSpec lhs specs e 
  return (i, e')

replaceExprWithSpec :: Id -> [(Type, Id)] -> CoreExpr -> CoreM CoreExpr
replaceExprWithSpec lhs specs (App (App (Var i) (Type t)) _)
  | i == lhs && any (\(x, _) -> deBruijnize x == deBruijnize t) specs = do
      -- get the actual spec
      let Just new_id = lookup (deBruijnize t) (map (\(x, y) -> (deBruijnize x, y)) specs)
      return $ Var new_id 
replaceExprWithSpec lhs specs (App f x) = do
  f' <- replaceExprWithSpec lhs specs f
  x' <- replaceExprWithSpec lhs specs x
  return $ App f' x'
replaceExprWithSpec lhs specs (Lam b e) = do
  e' <- replaceExprWithSpec lhs specs e
  return $ Lam b e'
replaceExprWithSpec lhs specs (Let b e) = do
  b' <- replaceBindWithSpec lhs specs b
  e' <- replaceExprWithSpec lhs specs e
  return $ Let b' e'

replaceExprWithSpec lhs specs (Case e b t alts) = do
  e' <- replaceExprWithSpec lhs specs e
  alts' <- mapM (replaceAltsWithSpec lhs specs) alts
  return $ Case e' b t alts'
replaceExprWithSpec lhs specs (Cast e c) = do
  e' <- replaceExprWithSpec lhs specs e
  return $ Cast e' c
replaceExprWithSpec lhs specs (Tick c e) = do
  e' <- replaceExprWithSpec lhs specs e
  return $ Tick c e'
replaceExprWithSpec _ _ e = return e

replaceAltsWithSpec :: Id -> [(Type, Id)] -> Alt Var -> CoreM (Alt Var)
replaceAltsWithSpec lhs specs (Alt ac ls e) = do 
  e' <- replaceExprWithSpec lhs specs e
  return $ Alt ac ls e'
  


