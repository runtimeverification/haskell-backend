{-# LANGUAGE Strict #-}

module Test.Kore.Internal.OrCondition (
    OrTestCondition,
    module Kore.Internal.OrCondition,
) where

import Kore.Internal.OrCondition
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )

type OrTestCondition = OrCondition RewritingVariableName
