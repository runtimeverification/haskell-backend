module Test.Kore.Internal.Condition
    ( TestCondition
    , module Kore.Internal.Condition
    ) where

import Kore.Internal.Condition
import Kore.Rewriting.RewritingVariable (RewritingVariableName)

type TestCondition = Condition RewritingVariableName
