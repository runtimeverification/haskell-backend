{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Simplify.Predicate (
    simplify,
) where

import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiOr (
    MultiOr,
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify

-- TODO (thomas.tuegel): Remove this file when the TermLike simplifier no longer
-- depends on the Condition simplifier.

type NormalForm = MultiOr (MultiAnd (Predicate RewritingVariableName))

simplify ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Predicate RewritingVariableName ->
    simplifier NormalForm
