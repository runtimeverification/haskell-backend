module Test.Kore.Internal.OrCondition
    ( OrTestCondition
    , module Kore.Internal.OrCondition
    ) where

import Kore.Internal.OrCondition
import Kore.Syntax.Variable

type OrTestCondition = OrCondition VariableName
