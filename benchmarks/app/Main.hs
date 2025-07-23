{-# OPTIONS_GHC -O2 #-}
{-# OPTIONS_GHC -ddump-simpl #-}
{-# OPTIONS_GHC -ddump-to-file #-}

module Main where

import Criterion.Main
import Data.Company
import Data.Expr (mkExpr)
import Data.Tree
import Hand.AnonNames
import Hand.DropCasts
import Hand.IncInt
import Hand.IncSalary
import Hand.NumTypes
import Hand.RenumberInt
import Hand.RmWeights
import Hand.SelectFloat
import Hand.SelectInt
import SYB.AnonNames
import SYB.DropCasts
import SYB.IncInt
import SYB.IncSalary
import SYB.NumTypes
import SYB.RenumberInt
import SYB.RmWeights
import SYB.SelectFloat
import SYB.SelectInt
import SYB35.AnonNames
import SYB35.DropCasts
import SYB35.IncInt
import SYB35.IncSalary
import SYB35.NumTypes
import SYB35.RenumberInt
import SYB35.RmWeights
import SYB35.SelectFloat
import SYB35.SelectInt
import SYB35Opt.AnonNames
import SYB35Opt.DropCasts
import SYB35Opt.IncInt
import SYB35Opt.IncSalary
import SYB35Opt.NumTypes
import SYB35Opt.RenumberInt
import SYB35Opt.RmWeights
import SYB35Opt.SelectFloat
import SYB35Opt.SelectInt
import SYBOpt.AnonNames
import SYBOpt.DropCasts
import SYBOpt.IncInt
import SYBOpt.IncSalary
import SYBOpt.NumTypes
import SYBOpt.RenumberInt
import SYBOpt.RmWeights
import SYBOpt.SelectFloat
import SYBOpt.SelectInt
import SYBPEOnly.AnonNames
import SYBPEOnly.DropCasts
import SYBPEOnly.IncInt
import SYBPEOnly.IncSalary
import SYBPEOnly.NumTypes
import SYBPEOnly.RenumberInt
import SYBPEOnly.RmWeights
import SYBPEOnly.SelectFloat
import SYBPEOnly.SelectInt

main :: IO ()
main =
  defaultMain
    [ bgroup
        "RmWeights"
        [ bench "Hand" $ nf rmWeights₁ (bigwtree 10),
          bench "SYB" $ nf rmWeights₂ (bigwtree 10),
          bench "SYB (PE only)" $ nf rmWeights₃ (bigwtree 10),
          bench "SYB (full opt)" $ nf rmWeights₄ (bigwtree 10),
          bench "SYB3.5" $ nf rmWeights₅ (bigwtree 10),
          bench "SYB3.5 (PE only)" $ nf rmWeights₆ (bigwtree 10)
        ],
      bgroup
        "IncSalary"
        [ bench "Hand" $ nf (incSalary₁ 0.1) (mkCompany 100),
          bench "SYB" $ nf (incSalary₂ 0.1) (mkCompany 100),
          bench "SYB (PE only)" $ nf (incSalary₃ 0.1) (mkCompany 100),
          bench "SYB (full opt)" $ nf (incSalary₄ 0.1) (mkCompany 100),
          bench "SYB3.5" $ nf (incSalary₅ 0.1) (mkCompany 100),
          bench "SYB3.5 (PE only)" $ nf (incSalary₆ 0.1) (mkCompany 100)
        ],
      bgroup
        "IncInt"
        [ bench "Hand" $ nf incInt₁ (mkExpr 20),
          bench "SYB" $ nf incInt₂ (mkExpr 20),
          bench "SYB (PE only)" $ nf incInt₃ (mkExpr 20),
          bench "SYB (full opt)" $ nf incInt₄ (mkExpr 20),
          bench "SYB3.5" $ nf incInt₅ (mkExpr 20),
          bench "SYB3.5 (PE only)" $ nf incInt₆ (mkExpr 20)
        ],
      bgroup
        "SelectInt"
        [ bench "Hand" $ nf selectInt₁ (bigwtree 10),
          bench "SYB" $ nf selectInt₂ (bigwtree 10),
          bench "SYB (PE only)" $ nf selectInt₃ (bigwtree 10),
          bench "SYB (full opt)" $ nf selectInt₄ (bigwtree 10),
          bench "SYB3.5" $ nf selectInt₅ (bigwtree 10),
          bench "SYB3.5 (PE only)" $ nf selectInt₆ (bigwtree 10)
        ],
      bgroup
        "SelectFloat"
        [ bench "Hand" $ nf selectFloat₁ (mkCompany 100),
          bench "SYB" $ nf selectFloat₂ (mkCompany 100),
          bench "SYB (PE only)" $ nf selectFloat₃ (mkCompany 100),
          bench "SYB (full opt)" $ nf selectFloat₄ (mkCompany 100),
          bench "SYB3.5" $ nf selectFloat₅ (mkCompany 100),
          bench "SYB3.5 (PE only)" $ nf selectFloat₆ (mkCompany 100)
        ],
      bgroup
        "NumTypes"
        [ bench "Hand" $ nf numTypes₁ (mkExpr 20),
          bench "SYB" $ nf numTypes₂ (mkExpr 20),
          bench "SYB (PE only)" $ nf numTypes₃ (mkExpr 20),
          bench "SYB (full opt)" $ nf numTypes₄ (mkExpr 20),
          bench "SYB3.5" $ nf numTypes₅ (mkExpr 20),
          bench "SYB3.5 (PE only)" $ nf numTypes₆ (mkExpr 20)
        ],
      bgroup
        "RenumberInt"
        [ bench "Hand" $ nf (renumberInt₁ 0) (bigwtree 10),
          bench "SYB" $ nf (renumberInt₂ 0) (bigwtree 10),
          bench "SYB (PE only)" $ nf (renumberInt₃ 0) (bigwtree 10),
          bench "SYB (full opt)" $ nf (renumberInt₄ 0) (bigwtree 10),
          bench "SYB3.5" $ nf (renumberInt₅ 0) (bigwtree 10),
          bench "SYB3.5 (PE only)" $ nf (renumberInt₆ 0) (bigwtree 10)
        ],
      bgroup
        "AnonNames"
        [ bench "Hand" $ nf anonNames₁ (mkCompany 100),
          bench "SYB" $ nf anonNames₂ (mkCompany 100),
          bench "SYB (PE only)" $ nf anonNames₃ (mkCompany 100),
          bench "SYB (full opt)" $ nf anonNames₄ (mkCompany 100),
          bench "SYB3.5" $ nf anonNames₅ (mkCompany 100),
          bench "SYB3.5 (full opt)" $ nf anonNames₆ (mkCompany 100)
        ],
      bgroup
        "DropCasts"
        [ bench "Hand" $ nf dropCasts₁ (mkExpr 20),
          bench "SYB" $ nf dropCasts₂ (mkExpr 20),
          bench "SYB (PE only)" $ nf dropCasts₃ (mkExpr 20),
          bench "SYB (full opt)" $ nf dropCasts₄ (mkExpr 20),
          bench "SYB3.5" $ nf dropCasts₅ (mkExpr 20),
          bench "SYB3.5 (PE only)" $ nf dropCasts₆ (mkExpr 20)
        ]
    ]
