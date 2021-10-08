module Test.Kore.Internal.OrCondition (
    OrTestCondition,
    module Kore.Internal.OrCondition,
) where

import Kore.Internal.OrCondition
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )

type OrTestCondition = OrCondition RewritingVariableName
