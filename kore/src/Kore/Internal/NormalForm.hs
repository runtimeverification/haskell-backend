{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Internal.NormalForm (
    NormalForm,
    toOrPattern,
    fromOrCondition,
    toOrCondition,
    fromPredicate,
    fromPredicates,
) where

import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.MultiOr (
    MultiOr,
 )
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern (
    Condition,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Syntax (
    Sort,
 )
import Prelude.Kore

{- | @NormalForm@ is the normal form result of simplifying 'Predicate'.
 The primary purpose of this form is to transmit to the external solver.
 Note that this is almost, but not quite, disjunctive normal form; see
 'Kore.Simplify.Predicate.simplifyNot' for the most notable exception.
-}
type NormalForm = MultiOr (MultiAnd (Predicate RewritingVariableName))

toOrPattern :: Sort -> NormalForm -> OrPattern RewritingVariableName
toOrPattern sort =
    MultiOr.map
        ( Pattern.fromPredicateSorted sort
            . Predicate.makeMultipleAndPredicate
            . toList
        )

fromOrCondition :: OrCondition RewritingVariableName -> NormalForm
fromOrCondition = MultiOr.map (from @(Condition _))

toOrCondition ::
    MultiOr (MultiAnd (Predicate RewritingVariableName)) ->
    OrCondition RewritingVariableName
toOrCondition =
    MultiOr.map (from @_ @(Condition _) . Predicate.fromMultiAnd)

fromPredicate :: Predicate RewritingVariableName -> NormalForm
fromPredicate = MultiOr.singleton . Predicate.toMultiAnd

fromPredicates :: [Predicate RewritingVariableName] -> NormalForm
fromPredicates = MultiOr.singleton . MultiAnd.make
