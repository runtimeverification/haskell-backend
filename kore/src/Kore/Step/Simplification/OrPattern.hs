{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.OrPattern
    ( simplifyConditionsWithSmt
    ) where

import qualified Control.Comonad as Comonad

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
import Kore.Internal.Predicate
    ( makeAndPredicate
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( toPredicate
    , top
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    , simplifyCondition
    )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
    ( filterMultiOr
    )

simplifyConditionsWithSmt
    ::  forall variable simplifier
    .   (MonadSimplify simplifier, SimplifierVariable variable)
    => SideCondition variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyConditionsWithSmt sideCondition unsimplified = do
    simplifiedWrappedPatterns <-
        fmap MultiOr.make . BranchT.gather $ do
            unsimplified1 <- BranchT.scatter unsimplified
            simplified <- simplifyCondition sideCondition unsimplified1
            -- Wrapping the original patterns as their own terms in order to be
            -- able to retrieve them unchanged after adding the sideCondition
            -- to them, simplification and SMT filtering
            let wrapped = addPredicate $ conditionalAsTerm simplified
            simplifyCondition SideCondition.top wrapped
    filteredWrappedPatterns <-
        SMT.Evaluator.filterMultiOr simplifiedWrappedPatterns
    return (MultiOr.filterOr (Conditional.term <$> filteredWrappedPatterns))
  where
    conditionalAsTerm
        :: Pattern variable -> Conditional variable (Pattern variable)
    conditionalAsTerm = Comonad.duplicate

    sidePredicate = SideCondition.toPredicate sideCondition

    addPredicate :: Conditional variable term -> Conditional variable term
    addPredicate c@Conditional {predicate} =
        c {Conditional.predicate = makeAndPredicate predicate sidePredicate}
