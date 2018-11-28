module Kore.Step.Pattern
    ( StepPattern
    , CommonStepPattern
    , ConcreteStepPattern
    , StepPatternHead
    , module Kore.AST.Pure
    ) where

import           Kore.AST.Pure
                 ( Concrete, Pattern, PurePattern, Variable )
import qualified Kore.Domain.Builtin as Domain

type StepPattern lvl var = PurePattern lvl Domain.Builtin var ()

type CommonStepPattern lvl = StepPattern lvl Variable

type ConcreteStepPattern lvl = StepPattern lvl Concrete

type StepPatternHead lvl var = Pattern lvl Domain.Builtin var
