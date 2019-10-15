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

import qualified Data.Foldable as Foldable

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
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
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import Kore.Internal.Pattern
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )
import qualified Kore.Step.Substitution as Substitution

simplifyEvaluatedMultiPredicate
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => MultiAnd (OrPredicate variable)
    -> simplifier (OrPredicate variable)
simplifyEvaluatedMultiPredicate predicates = do
    let
        crossProduct :: MultiOr [Predicate variable]
        crossProduct =
            MultiOr.fullCrossProduct
                (MultiAnd.extractPatterns predicates)
    orResults <- BranchT.gather (traverse andPredicates crossProduct)
    return (MultiOr.mergeAll orResults)
  where
    andPredicates
        :: [Predicate variable]
        -> BranchT simplifier (Predicate variable)
    andPredicates predicates' =
        fmap markSimplified
        $ Substitution.normalize (Foldable.fold predicates')
      where
        markSimplified
          | all Predicate.isSimplified predicates' = Predicate.markSimplified
          | otherwise = id
