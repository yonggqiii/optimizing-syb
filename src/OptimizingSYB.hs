{-# LANGUAGE LambdaCase #-}
module OptimizingSYB(plugin) where

import GHC.Plugins
import Pass.PartialEval(specByPartialEvaluation)
import Pass.Memo(memoizedSpecialize)
import Pass.CastCase(castCase)
import Pass.SimpleInlinings(simpleInlinings)
import Pass.Pepsa(pepsa)
import Utils (parseCommandLineOpts)

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  , pluginRecompile = purePlugin
}

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install c todo = do
    opts <- parseCommandLineOpts c
    -- return $ [simpleInlinings opts, memoizedSpecialize opts] ++ simplify ++ (specByPartialEvaluation opts : todo)
    -- return $ [memoizedSpecialize opts] ++ simplify ++ (specByPartialEvaluation opts : todo)
    -- return $ [simpleInlinings opts, pepsa opts] ++ simplify ++ (specByPartialEvaluation opts : simplify) ++ (castCase opts : todo)
    -- return $ [simpleInlinings opts, pepsa opts] ++ simplify ++ (specByPartialEvaluation opts : simplify) ++ (castCase opts : todo)
    return $ simplify ++ (pepsa opts : todo)
  where simplify = filter (\case 
                          CoreDoSimplify {} -> True
                          _ -> False) todo

