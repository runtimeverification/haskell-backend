module Test.Kore.Internal.SideCondition
    ( TestSideCondition
    , module Kore.Internal.SideCondition
    ) where

import Kore.Internal.SideCondition
import Kore.Syntax.Variable

type TestSideCondition = SideCondition VariableName
