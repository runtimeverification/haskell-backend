{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplifyAndRemoveTopExists
    , simplify
    , simplifyPredicate
    ) where

import qualified Control.Monad.Trans.Class as Monad.Trans

import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
                 ( pattern Exists_ )
import           Kore.Logger
                 ( LogMessage, WithLog )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( simplify )
import qualified Kore.Step.Merging.Pattern as Pattern
import           Kore.Step.Simplification.Data
                 ( BranchT, MonadSimplify, SimplifierVariable )
import qualified Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )

simplifyAndRemoveTopExists
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)
simplifyAndRemoveTopExists patt = do
    simplified <- simplify patt
    return (removeTopExists <$> simplified)
  where
    removeTopExists :: Pattern variable -> Pattern variable
    removeTopExists p@Conditional{ term = Exists_ _ _ quantified } =
        removeTopExists p {term = quantified}
    removeTopExists p = p

{-| Simplifies an 'Pattern', returning an 'OrPattern'.
-}
simplify
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)
simplify pattern'@Conditional { term } = do
    simplifiedTerm <- Simplifier.simplifyTerm term
    orPatterns <-
        BranchT.gather
        $ traverse
            (Pattern.mergeWithPredicate $ Pattern.withoutTerm pattern')
            simplifiedTerm
    return (MultiOr.mergeAll orPatterns)

{-| Simplifies the predicate inside an 'Pattern'.
-}
simplifyPredicate
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -- ^ The condition to be evaluated.
    -> BranchT simplifier (Pattern variable)
simplifyPredicate Conditional {term, predicate, substitution} = do
    evaluated <- Monad.Trans.lift $ Predicate.simplify predicate
    let Conditional { predicate = evaluatedPredicate } = evaluated
        Conditional { substitution = evaluatedSubstitution } = evaluated
    merged <-
        mergePredicatesAndSubstitutions
            [evaluatedPredicate]
            [substitution, evaluatedSubstitution]
    -- TODO(virgil): Do I need to re-evaluate the predicate?
    return $ Pattern.withCondition term merged
