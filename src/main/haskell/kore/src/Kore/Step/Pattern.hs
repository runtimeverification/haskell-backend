module Kore.Step.Pattern
    ( StepPattern
    , CommonStepPattern
    , ConcreteStepPattern
    , StepPatternHead
    , module Kore.AST.Pure
    ) where

import           Kore.Annotation.Valid
import           Kore.AST.Pure
                 ( Concrete, Pattern, PurePattern, Variable )
import qualified Kore.Domain.Builtin as Domain

type StepPattern level variable =
    PurePattern level Domain.Builtin variable (Valid level)

type CommonStepPattern level = StepPattern level Variable

type ConcreteStepPattern level = StepPattern level Concrete

type StepPatternHead level variable = Pattern level Domain.Builtin variable
