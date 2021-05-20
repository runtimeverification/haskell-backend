{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.Condition (
    create,
    simplify,
    simplifyPredicate,
    simplifyCondition,
    -- For testing
    simplifyPredicates,
) where

import Changed
import qualified Control.Lens as Lens
import Control.Monad.State.Strict (
    StateT,
 )
import qualified Control.Monad.State.Strict as State
import Data.Generics.Product (
    field,
 )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Condition,
    Conditional (..),
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.Simplify
import Kore.Step.Simplification.SubstitutionSimplifier (
    SubstitutionSimplifier (..),
 )
import qualified Kore.TopBottom as TopBottom
import Kore.Unparser
import Logic
import Prelude.Kore
import qualified Pretty

-- | Create a 'ConditionSimplifier' using 'simplify'.
create ::
    MonadSimplify simplifier =>
    SubstitutionSimplifier simplifier ->
    ConditionSimplifier simplifier
create substitutionSimplifier =
    ConditionSimplifier $ simplify substitutionSimplifier

{- | Simplify a 'Condition'.

@simplify@ applies the substitution to the predicate and simplifies the
result. The result is re-simplified until it stabilizes.

The 'term' of 'Conditional' may be any type; it passes through @simplify@
unmodified.
-}
simplify ::
    forall simplifier any.
    ( HasCallStack
    , MonadSimplify simplifier
    ) =>
    SubstitutionSimplifier simplifier ->
    SideCondition RewritingVariableName ->
    Conditional RewritingVariableName any ->
    LogicT simplifier (Conditional RewritingVariableName any)
simplify SubstitutionSimplifier{simplifySubstitution} sideCondition =
    normalize >=> worker
  where
    worker Conditional{term, predicate, substitution} = do
        let substitution' = Substitution.toMap substitution
            predicate' = Predicate.substitute substitution' predicate

        simplified <-
            simplifyPredicate sideCondition predicate'
                >>= simplifyPredicates sideCondition . from @_ @(MultiAnd _)
        TopBottom.guardAgainstBottom simplified
        let merged = simplified <> Condition.fromSubstitution substitution
        normalized <- normalize merged
        -- Check for full simplification *after* normalization. Simplification
        -- may have produced irrelevant substitutions that become relevant after
        -- normalization.
        let simplifiedPattern =
                Lens.traverseOf
                    (field @"predicate")
                    simplifyConjunctions
                    normalized{term}
        if fullySimplified simplifiedPattern
            then return (extract simplifiedPattern)
            else worker (extract simplifiedPattern)

    -- TODO(Ana): this should also check if the predicate is simplified
    fullySimplified (Unchanged Conditional{predicate, substitution}) =
        Predicate.isFreeOf predicate variables
      where
        variables = Substitution.variables substitution
    fullySimplified (Changed _) = False

    normalize ::
        forall any'.
        Conditional RewritingVariableName any' ->
        LogicT simplifier (Conditional RewritingVariableName any')
    normalize conditional@Conditional{substitution} = do
        let conditional' = conditional{substitution = mempty}
        predicates' <-
            lift $
                simplifySubstitution sideCondition substitution
        predicate' <- scatter predicates'
        return $ Conditional.andCondition conditional' predicate'

simplifyPredicates ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    MultiAnd (Predicate RewritingVariableName) ->
    LogicT simplifier (Condition RewritingVariableName)
simplifyPredicates sideCondition original = do
    let predicates =
            SideCondition.simplifyConjunctionByAssumption original
                & fst . extract
    simplified <-
        simplifyPredicatesWithAssumptions
            sideCondition
            (toList predicates)
    if original == from simplified
        then return (Condition.markSimplified simplified)
        else simplifyPredicates sideCondition (from simplified)

simplifyPredicatesWithAssumptions ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    [Predicate RewritingVariableName] ->
    LogicT
        simplifier
        (Condition RewritingVariableName)
simplifyPredicatesWithAssumptions _ [] = return Condition.top
simplifyPredicatesWithAssumptions sideCondition predicates@(_ : rest) = do
    let predicatesWithUnsimplified =
            zip predicates $
                scanr ((<>) . MultiAnd.singleton) MultiAnd.top rest
    State.execStateT
        ( traverse
            simplifyWithAssumptions
            predicatesWithUnsimplified
        )
        Condition.top
  where
    simplifyWithAssumptions ::
        ( Predicate RewritingVariableName
        , MultiAnd (Predicate RewritingVariableName)
        ) ->
        StateT
            (Condition RewritingVariableName)
            (LogicT simplifier)
            ()
    simplifyWithAssumptions (predicate, unsimplifiedSideCond) = do
        simplifiedSideCond <- State.get
        let otherSideConds =
                SideCondition.addPredicates
                    (from simplifiedSideCond <> unsimplifiedSideCond)
                    sideCondition
        result <- lift $ simplifyPredicate otherSideConds predicate
        State.put (simplifiedSideCond <> result)

{- | Simplify the 'Predicate' once.

@simplifyPredicate@ does not attempt to apply the resulting substitution and
re-simplify the result.

See also: 'simplify'
-}
simplifyPredicate ::
    ( HasCallStack
    , MonadSimplify simplifier
    ) =>
    SideCondition RewritingVariableName ->
    Predicate RewritingVariableName ->
    LogicT simplifier (Condition RewritingVariableName)
simplifyPredicate sideCondition predicate = do
    patternOr <-
        lift $
            simplifyTermLike sideCondition $
                Predicate.fromPredicate_ predicate
    -- Despite using lift above, we do not need to
    -- explicitly check for \bottom because patternOr is an OrPattern.
    scatter (OrPattern.map eraseTerm patternOr)
  where
    eraseTerm conditional
        | TopBottom.isTop (Pattern.term conditional) =
            Conditional.withoutTerm conditional
        | otherwise =
            (error . show . Pretty.vsep)
                [ "Expecting a \\top term, but found:"
                , unparse conditional
                ]

simplifyConjunctions ::
    Predicate RewritingVariableName ->
    Changed (Predicate RewritingVariableName)
simplifyConjunctions original@(MultiAnd.fromPredicate -> predicates) =
    case SideCondition.simplifyConjunctionByAssumption predicates of
        Unchanged _ -> Unchanged original
        Changed (changed, _) ->
            Changed (MultiAnd.toPredicate changed)
