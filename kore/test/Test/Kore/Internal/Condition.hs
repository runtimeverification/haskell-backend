module Test.Kore.Internal.Condition (
    TestCondition,
    module Kore.Internal.Condition,
) where

import Kore.Internal.Condition
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )

type TestCondition = Condition RewritingVariableName
