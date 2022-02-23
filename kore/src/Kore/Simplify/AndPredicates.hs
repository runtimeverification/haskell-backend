{- |
Module      : Kore.Simplify.AndPredicates
Description : Tools for And Predicate simplification.
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.AndPredicates (
    simplifyEvaluatedMultiPredicate,
) where

import Kore.Internal.Condition qualified as Condition
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Rewrite.Substitution qualified as Substitution
import Kore.Simplify.Simplify (
    MonadSimplify,
 )
import Logic qualified as LogicT
import Prelude.Kore

simplifyEvaluatedMultiPredicate ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    MultiAnd (OrCondition RewritingVariableName) ->
    simplifier (OrCondition RewritingVariableName)
simplifyEvaluatedMultiPredicate sideCondition predicates =
    MultiOr.observeAllT $ do
        element <- MultiAnd.traverse LogicT.scatter predicates
        andConditions element
  where
    andConditions predicates' =
        fmap markSimplified $
            Substitution.normalize sideCondition (fold predicates')
      where
        markSimplified =
            Condition.setPredicateSimplified
                (foldMap Condition.simplifiedAttribute predicates')
