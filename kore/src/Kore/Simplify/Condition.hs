{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Simplify.Condition (
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
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Predicate as Predicate
import Kore.Simplify.Simplify
import Kore.Simplify.SubstitutionSimplifier (
    SubstitutionSimplifier (..),
 )
import Kore.Substitute
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
            predicate' = substitute substitution' predicate

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
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    MultiAnd (Predicate RewritingVariableName) ->
    LogicT simplifier (Condition RewritingVariableName)
simplifyPredicates sideCondition original = do
    let predicates =
            SideCondition.simplifyConjunctionByAssumption original
                & fst . extract
    simplifiedPredicates <-
        simplifyPredicatesWithAssumptions
            sideCondition
            (toList predicates)
    let simplified = foldMap mkCondition simplifiedPredicates
    if original == simplifiedPredicates
        then return (Condition.markSimplified simplified)
        else simplifyPredicates sideCondition simplifiedPredicates

{- | Simplify a conjunction of predicates by simplifying each one
under the assumption that the others are true.
-}
simplifyPredicatesWithAssumptions ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    [Predicate RewritingVariableName] ->
    LogicT
        simplifier
        (MultiAnd (Predicate RewritingVariableName))
simplifyPredicatesWithAssumptions _ [] = return MultiAnd.top
simplifyPredicatesWithAssumptions sideCondition predicates@(_ : rest) = do
    let unsimplifieds =
            map MultiAnd.singleton rest
                & scanr (<>) MultiAnd.top
    traverse_ simplifyWithAssumptions (zip predicates unsimplifieds)
        & flip State.execStateT MultiAnd.top
  where
    simplifyWithAssumptions ::
        ( Predicate RewritingVariableName
        , MultiAnd (Predicate RewritingVariableName)
        ) ->
        StateT
            (MultiAnd (Predicate RewritingVariableName))
            (LogicT simplifier)
            ()
    simplifyWithAssumptions (predicate, unsimplifiedSideCond) = do
        sideCondition' <- getSideCondition unsimplifiedSideCond
        result <- simplifyPredicate sideCondition' predicate
        putSimplifiedResult result

    getSideCondition unsimplifiedSideCond = do
        simplifiedSideCond <- State.get
        SideCondition.addAssumptions
            (simplifiedSideCond <> unsimplifiedSideCond)
            sideCondition
            & return

    putSimplifiedResult result = State.modify' (<> result)

    simplifyPredicate sideCondition' predicate =
        Predicate.simplify sideCondition' predicate >>= Logic.scatter & lift

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
