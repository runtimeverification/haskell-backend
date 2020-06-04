module Test.Kore.Internal.Condition
    ( TestCondition
    , module Kore.Internal.Condition
    ) where

import Kore.Internal.Condition
import Kore.Syntax.Variable

type TestCondition = Condition VariableName
