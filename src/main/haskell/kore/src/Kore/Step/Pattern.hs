module Kore.Step.Pattern
    ( StepPattern
    , CommonStepPattern
    , ConcreteStepPattern
    , StepPatternHead
    ) where

import           Kore.AST.Common
                 ( Concrete, Pattern, PureMLPattern, Variable )
import qualified Kore.Domain.Builtin as Domain

type StepPattern lvl var = PureMLPattern lvl Domain.Builtin var

type CommonStepPattern lvl = StepPattern lvl Variable

type ConcreteStepPattern lvl = StepPattern lvl Concrete

type StepPatternHead lvl var = Pattern lvl Domain.Builtin var
