module OptimizingSYB(plugin) where

import GHC.Plugins
import Pass.PartialEval(specByPartialEvaluation)
import Pass.Memo(memoizedSpecialize)
import Pass.SimpleInlinings(simpleInlinings)
import Utils (parseCommandLineOpts)

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install c todo = do
  opts <- parseCommandLineOpts c
  putMsgS $ show opts
  -- For now, simpl, then remove sameTypeRep, then simpl and do again
  return $ [simpleInlinings opts, memoizedSpecialize] ++ todo ++ (specByPartialEvaluation opts : todo) -- ++ (specByPartialEvaluation : todo)
  -- return todo
  -- return []
