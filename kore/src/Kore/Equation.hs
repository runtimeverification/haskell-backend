{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Equation (
    module Kore.Equation.Equation,
    fromSentenceAxiom,
    extractEquations,
    simplifyExtractedEquations,
    module Kore.Equation.Application,
) where

import Kore.Equation.Application
import Kore.Equation.Equation
import Kore.Equation.Registry
import Kore.Equation.Sentence
import Kore.Equation.Simplification
