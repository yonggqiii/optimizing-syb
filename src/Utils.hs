module Utils where
import GHC.Plugins hiding ((<>))
import GHC.Utils.Ppr.Colour
import Control.Monad
data Opts = Opts { show_simple :: Bool
                 , show_fn_map :: Bool
                 , show_traversal_extraction :: Bool
                 , show_scheme_elim :: Bool
                 , show_gmap_elim :: Bool
                 , show_spec :: Bool
                 , show_type_eval :: Bool
                 }
  deriving (Show, Eq)

parseCommandLineOpts :: [CommandLineOption] -> CoreM Opts
parseCommandLineOpts [] 
  = return Opts { show_simple = False
                , show_fn_map = False
                , show_traversal_extraction = False
                , show_scheme_elim = False
                , show_gmap_elim = False
                , show_spec = False
                , show_type_eval = False
                }
parseCommandLineOpts (x : xs)
  = do opts <- parseCommandLineOpts xs
       case x of 
          "--show-simple" -> return opts { show_simple = True }
          "--show-function-map" -> return opts { show_fn_map = True }
          "--show-traversal-extraction" -> return opts { show_traversal_extraction = True }
          "--show-scheme-elim" -> return opts { show_scheme_elim = True }
          "--show-gmap-elim" -> return opts { show_gmap_elim = True }
          "--show-spec" -> return opts { show_spec = True }
          "--show-type-eval" -> return opts { show_type_eval = True }
          "--verbose" -> return Opts { show_simple = True
                                      , show_fn_map = True
                                      , show_traversal_extraction = True
                                      , show_scheme_elim = True
                                      , show_gmap_elim = True
                                      , show_spec = True
                                      , show_type_eval = True
                                      }
          _ -> putMsgS (warn ("Unknown option for OptimizingSYB: " ++ x)) >> return opts

box :: Int -> String -> PprColour -> String
box width s color = let top = renderColour color ++ "┏" ++ replicate (width + 2) '━' ++ "┓\n"
                        mid = renderColour color ++ "┃ " ++ renderColour colReset ++ s ++ renderColour color ++ " ┃\n"
                        bot = "┗" ++ replicate (width + 2) '━' ++ "┛" ++ renderColour colReset
                    in top ++ mid ++ bot


warn :: String -> String
warn s
  = let color = colBold <> colMagentaFg
        reset = colReset
        width = length $ "[WARN]: " ++ s
    in box width ("[" ++ renderColour color ++ "WARN" ++ renderColour reset ++ "]: " ++ s) colMagentaFg

info :: String -> String
info s 
  = let color = colBold <> colCyanFg
        reset = colReset
        width = length $ "[INFO]: " ++ s
    in box width ("[" ++ renderColour color ++ "INFO" ++ renderColour reset ++ "]: " ++ s) colCyanFg

success :: String -> String
success s 
  = let color = colBold <> colGreenFg
        reset = colReset
        width = length $ "[SUCCESS]: " ++ s
    in box width ("[" ++ renderColour color ++ "SUCCESS" ++ renderColour reset ++ "]: " ++ s) colGreenFg

prt :: forall a. Outputable a => a -> CoreM ()
prt = putMsg . ppr

prtIf :: forall a. Outputable a => Bool -> a -> CoreM ()
prtIf b x = when b $ prt x 

prtSIf :: Bool -> String -> CoreM ()
prtSIf b x = when b $ putMsgS x
