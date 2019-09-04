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

import           Kore.Internal.MultiAnd
                 ( MultiAnd )
import qualified Kore.Internal.MultiAnd as MultiAnd
                 ( extractPatterns )
import           Kore.Internal.MultiOr
                 ( MultiOr )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( fullCrossProduct, mergeAll )
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import           Kore.Internal.Pattern
                 ( Predicate )
import           Kore.Step.Simplification.Data
                 ( BranchT, MonadSimplify, SimplifierVariable )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
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
        Substitution.normalize (Foldable.fold predicates')
