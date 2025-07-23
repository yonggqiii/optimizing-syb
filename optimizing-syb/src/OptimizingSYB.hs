{-# LANGUAGE LambdaCase #-}

module OptimizingSYB (plugin) where

import GHC.Plugins
-- import Pass.CastCase (castCase)
-- import Pass.Memo (memoizedSpecialize)
import Pass.PartialEval (specByPartialEvaluation)
import Pass.Pepsa (pepsa)
-- import Pass.SimpleInlinings (simpleInlinings)
import Utils

plugin :: Plugin
plugin =
  defaultPlugin
    { installCoreToDos = install,
      pluginRecompile = purePlugin
    }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install c todo = do
  opts <- parseCommandLineOpts c
  -- return $ [simpleInlinings opts, memoizedSpecialize opts] ++ simplify ++ (specByPartialEvaluation opts : todo)
  -- return $ [memoizedSpecialize opts] ++ simplify ++ (specByPartialEvaluation opts : todo)
  -- return $ [simpleInlinings opts, pepsa opts] ++ simplify ++ (specByPartialEvaluation opts : simplify) ++ (castCase opts : todo)
  -- return $ simplify ++ (pepsa opts : todo)
  -- return $ simplify ++ [pepsa opts, specByPartialEvaluation opts] ++ todo -- (specByPartialEvaluation opts : simplify) ++ todo
  if no_symb_exec opts
    then return $ simplify ++ [pepsa opts] ++ todo
    else
      return $ simplify ++ [pepsa opts] ++ simplify ++ [specByPartialEvaluation opts] ++ todo
  where
    simplify =
      filter
        ( \case
            CoreDoSimplify {} -> True
            _ -> False
        )
        todo
