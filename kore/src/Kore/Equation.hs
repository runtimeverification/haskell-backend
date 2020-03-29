{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation
    ( module Kore.Equation.Equation
    , fromSentenceAxiom
    , extractEquations
    , simplifyExtractedEquations
    ) where

import Kore.Equation.Equation
import Kore.Equation.Registry
import Kore.Equation.Sentence
import Kore.Equation.Simplification
