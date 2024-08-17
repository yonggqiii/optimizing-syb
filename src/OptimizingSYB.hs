module OptimizingSYB(plugin) where

import GHC.Plugins
import Pass.PartialEval(specByPartialEvaluation)
import Pass.Memo(memoizedSpecialize)
import Pass.SimpleInlinings(simpleInlinings)

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  -- For now, simpl, then remove sameTypeRep, then simpl and do again
  return $ [simpleInlinings, memoizedSpecialize] ++ todo ++ (specByPartialEvaluation : todo) -- ++ (specByPartialEvaluation : todo)
  -- return todo
