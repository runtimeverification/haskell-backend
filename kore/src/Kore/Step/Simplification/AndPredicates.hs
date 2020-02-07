{-|
Module      : Kore.Step.Simplification.AndPredicates
Description : Tools for And Predicate simplification.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.AndPredicates
    ( simplifyEvaluatedMultiPredicate
    ) where

import Prelude.Kore

import qualified Data.Foldable as Foldable

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( extractPatterns
    )
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
    ( fullCrossProduct
    , mergeAll
    )
import Kore.Internal.OrCondition
    ( OrCondition
    )
import Kore.Internal.Pattern
    ( Condition
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )
import qualified Kore.Step.Substitution as Substitution

simplifyEvaluatedMultiPredicate
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => SideCondition variable
    -> MultiAnd (OrCondition variable)
    -> simplifier (OrCondition variable)
simplifyEvaluatedMultiPredicate sideCondition predicates = do
    let
        crossProduct :: MultiOr [Condition variable]
        crossProduct =
            MultiOr.fullCrossProduct
                (MultiAnd.extractPatterns predicates)
    orResults <- BranchT.gather (traverse andConditions crossProduct)
    return (MultiOr.mergeAll orResults)
  where
    andConditions
        :: [Condition variable]
        -> BranchT simplifier (Condition variable)
    andConditions predicates' =
        fmap markSimplified
        $ Substitution.normalize sideCondition (Foldable.fold predicates')
      where
        markSimplified =
            Condition.setPredicateSimplified
                (Foldable.foldMap Condition.simplifiedAttribute predicates')
