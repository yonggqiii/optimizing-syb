module OptimizingSYB(plugin) where

import GHC.Plugins
import Pass.PartialEval(specByPartialEvaluation)
import Pass.Memo(memoizedSpecialize)
import Pass.SimpleInlinings(simpleInlinings)
import Utils (parseCommandLineOpts)

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  , pluginRecompile = purePlugin
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install c todo = do
  opts <- parseCommandLineOpts c
  return $ [simpleInlinings opts, memoizedSpecialize opts] ++ filter (\x -> case x of 
    CoreDoSimplify _ _ -> True
    _ -> False) todo ++ (specByPartialEvaluation opts : todo)

