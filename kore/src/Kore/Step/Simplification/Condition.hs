{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.Condition (
    create,
    simplify,
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
import Kore.Internal.Pattern (
    Condition,
    Conditional (..),
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Substitution (
    Assignment,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.Simplification.Predicate as Predicate
import Kore.Step.Simplification.Simplify
import Kore.Step.Simplification.SubstitutionSimplifier (
    SubstitutionSimplifier (..),
 )
import qualified Kore.TopBottom as TopBottom
import Logic
import Prelude.Kore

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
            Predicate.simplify sideCondition predicate'
                >>= Logic.scatter
                >>= simplifyPredicates sideCondition
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
            simplifySubstitution sideCondition substitution
                & lift
        predicate' <- scatter predicates'
        return $ Conditional.andCondition conditional' predicate'

{- | Simplify a conjunction of predicates by applying predicate and term
replacements and by simplifying each predicate with the assumption that the
others are true.
This procedure is applied until the conjunction stabilizes.
-}
simplifyPredicates ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    MultiAnd (Predicate RewritingVariableName) ->
    LogicT simplifier (Condition RewritingVariableName)
simplifyPredicates initialSideCondition predicates = do
    let predicatesList = toList predicates
        unsimplifieds = scanr ((<>) . MultiAnd.singleton) MultiAnd.top predicatesList
    simplifieds <-
        traverse worker (zip predicatesList unsimplifieds)
            & flip State.evalStateT initialSideCondition
    markConjunctionSimplified (foldMap mkCondition $ mconcat simplifieds)
  where
    worker ::
        ( Predicate RewritingVariableName
        , MultiAnd (Predicate RewritingVariableName)
        ) ->
        StateT
            (SideCondition RewritingVariableName)
            (LogicT simplifier)
            (MultiAnd (Predicate RewritingVariableName))
    worker (predicate, unsimplified) = do
        sideCondition <- SideCondition.addAssumptions unsimplified <$> State.get
        results <-
            Predicate.simplify sideCondition predicate >>= Logic.scatter
                & lift
        State.modify (SideCondition.addAssumptions results)
        return results

    markConjunctionSimplified =
        return . Lens.over (field @"predicate") Predicate.markSimplified

mkCondition ::
    InternalVariable variable =>
    Predicate variable ->
    Condition variable
mkCondition predicate =
    maybe
        (from @(Predicate _) predicate)
        (from @(Assignment _))
        (Substitution.retractAssignment predicate)

simplifyConjunctions ::
    Predicate RewritingVariableName ->
    Changed (Predicate RewritingVariableName)
simplifyConjunctions original@(MultiAnd.fromPredicate -> predicates) =
    case SideCondition.simplifyConjunctionByAssumption predicates of
        Unchanged _ -> Unchanged original
        Changed (changed, _) ->
            Changed (MultiAnd.toPredicate changed)
