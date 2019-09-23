{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.OrPattern
    ( simplifyPredicatesWithSmt
    ) where

import qualified Branch as BranchT
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Predicate.Predicate
    ( makeAndPredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Step.Simplification.Conditional as Conditional
    ( simplifyPredicate
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
    ( filterMultiOr
    )

simplifyPredicatesWithSmt
    ::  forall variable simplifier
    .   (MonadSimplify simplifier, SimplifierVariable variable)
    => Syntax.Predicate variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyPredicatesWithSmt predicate' unsimplified = do
    simplifiedWrappedPatterns <-
        fmap MultiOr.make . BranchT.gather $ do
            unsimplified1 <- BranchT.scatter unsimplified
            simplified <- Conditional.simplifyPredicate unsimplified1
            -- Wrapping the original patterns as their own terms in order to be
            -- able to retrieve them unchanged after adding predicate' to them,
            -- simplification and SMT filtering
            let wrapped = addPredicate $ conditionalAsTerm simplified
            resimplified <- Conditional.simplifyPredicate wrapped
            return resimplified
    filteredWrappedPatterns <-
        SMT.Evaluator.filterMultiOr simplifiedWrappedPatterns
    return (Conditional.term <$> filteredWrappedPatterns)
  where
    conditionalAsTerm
        :: Pattern variable -> Conditional variable (Pattern variable)
    conditionalAsTerm c = c {Conditional.term = c}

    addPredicate :: Conditional variable term -> Conditional variable term
    addPredicate c@Conditional {predicate} =
        c {Conditional.predicate = makeAndPredicate predicate predicate'}
