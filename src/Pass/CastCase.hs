module Pass.CastCase(castCase) where
import Engines.KnownCase(caseOfKnownCase)
import Engines.Substitution(substitute)
import Engines.LetInline(letInline)
import Engines.BetaReduction
import GHC.Plugins
import Control.Monad
import Data.Maybe 
import GHC.Core.Map.Type
import Engines.LeftElaboration
import Engines.Transform
import Engines.InlineUnfolding (inlineId)
import Utils 


-- | The memoized specializing pass specializes traversals.
castCase :: Opts ->  CoreToDo
castCase opts = CoreDoPluginPass "Cast-Case Elimination" (castCaseModGuts opts)

castCaseModGuts opts mod_guts = do
  let binds = mg_binds mod_guts
  binds' <- fullTransformM castCaseExpr binds
  return mod_guts {mg_binds = binds'}

castCaseExpr :: CoreExpr -> CoreM CoreExpr
castCaseExpr (Case (Cast e c) v t alts) = do
  let v_type = varType v
  if deBruijnize t == deBruijnize v_type
  then return $ Case e v t alts
  else return $ Case (Cast e c) v t alts
castCaseExpr e = return e
