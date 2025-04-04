{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.Condition (
    create,
    simplify,
    simplifyCondition,
    -- For testing
    simplifyPredicates,
) where

import Changed
import Control.Lens qualified as Lens
import Control.Monad.State.Strict (
    StateT,
 )
import Control.Monad.State.Strict qualified as State
import Data.Functor.Foldable qualified as Recursive
import Data.Generics.Product (
    field,
 )
import Data.Set (
    Set,
 )
import Kore.Attribute.Pattern.FreeVariables (
    freeVariableNames,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.Pattern (
    Condition,
    Conditional (..),
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Substitution (
    Assignment,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Log.WarnUnsimplified (
    warnUnsimplifiedCondition,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import {-# SOURCE #-} Kore.Simplify.Predicate qualified as Predicate
import Kore.Simplify.Simplify
import Kore.Simplify.SubstitutionSimplifier (
    SubstitutionSimplifier (..),
 )
import Kore.Substitute
import Kore.Syntax.Exists qualified as Exists
import Kore.Syntax.Variable (SomeVariableName)
import Kore.TopBottom qualified as TopBottom
import Logic
import Prelude.Kore

-- | Create a 'ConditionSimplifier' using 'simplify'.
create ::
    MonadSimplify simplifier =>
    SubstitutionSimplifier simplifier ->
    ConditionSimplifier simplifier
create substitutionSimplifier =
    ConditionSimplifier $ simplify substitutionSimplifier
{-# SPECIALIZE create ::
    SubstitutionSimplifier Simplifier ->
    ConditionSimplifier Simplifier
    #-}

{- | Simplify a 'Condition'.

@simplify@ applies the substitution to the predicate and simplifies the
result. The result is re-simplified until it stabilizes.

The 'term' of 'Conditional' may be any type; it passes through @simplify@
unmodified.
-}
simplify ::
    forall simplifier any.
    HasCallStack =>
    MonadSimplify simplifier =>
    SubstitutionSimplifier simplifier ->
    SideCondition RewritingVariableName ->
    Conditional RewritingVariableName any ->
    LogicT simplifier (Conditional RewritingVariableName any)
simplify SubstitutionSimplifier{simplifySubstitution} sideCondition original = do
    normOriginal <- normalize original
    (isFullySimplified, result) <- foldM simplifyingCondition (False, normOriginal) [1 .. limit]
    unless isFullySimplified $ warnUnsimplifiedCondition limit original result
    return result
  where
    limit :: Int
    limit = 10

    simplifyingCondition ::
        (Bool, Conditional RewritingVariableName any) ->
        Int ->
        LogicT simplifier (Bool, Conditional RewritingVariableName any)
    simplifyingCondition result@(True, _) _ = return result
    simplifyingCondition (_, input) _ = do
        output <- worker input
        return (fullySimplified output, extract output)

    worker Conditional{term, predicate, substitution} = do
        let substitution' = Substitution.toMap substitution
            predicate' = substitute substitution' predicate

        simplified <-
            simplifyPredicate predicate'
                >>= Logic.scatter
                >>= mapLogicT liftSimplifier . simplifyPredicates sideCondition . prepareForResimplification
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
        return simplifiedPattern

    simplifyPredicate predicate =
        Predicate.simplify sideCondition predicate & liftSimplifier

    prepareForResimplification predicates
        -- If the 'MultiAnd' is singular, we should avoid resimplification.
        | length predicates <= 1 =
            predicates
        | otherwise =
            MultiAnd.map forgetSimplified predicates
      where
        forgetSimplified p
            | Predicate.isSimplifiedAnyCondition p =
                Predicate.forgetSimplifiedSafe p
            | otherwise = p

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
{-# SPECIALIZE simplify ::
    forall any.
    HasCallStack =>
    SubstitutionSimplifier Simplifier ->
    SideCondition RewritingVariableName ->
    Conditional RewritingVariableName any ->
    LogicT Simplifier (Conditional RewritingVariableName any)
    #-}

{- | Simplify a conjunction of predicates by applying predicate and term
replacements and by simplifying each predicate with the assumption that the
others are true.
This procedure is applied until the conjunction stabilizes.
-}
simplifyPredicates ::
    SideCondition RewritingVariableName ->
    MultiAnd (Predicate RewritingVariableName) ->
    LogicT Simplifier (Condition RewritingVariableName)
simplifyPredicates sideCondition original = do
    let predicates =
            SideCondition.simplifyConjunctionByAssumption original
                & fst . extract
    simplifiedPredicates <- do
        let eliminatedExists =
                map
                    ( simplifyPredicateExistElim $
                        -- TODO (sam): this is quite conservative and we may not need to
                        -- avoid names here, but there doesn't seem to be a negative
                        -- impact on performance, so best leave this in for now.
                        freeVariableNames original
                            <> freeVariableNames sideCondition
                    )
                    $ toList predicates
        simplifyPredicatesWithAssumptions
            sideCondition
            eliminatedExists
    let simplified = foldMap mkCondition simplifiedPredicates
    if original == simplifiedPredicates
        then return (Condition.markSimplified simplified)
        else simplifyPredicates sideCondition simplifiedPredicates

{- | Simplify an existential predicate by removing the existential binder and refreshing
all occurrences of the name within the child term
-}
simplifyPredicateExistElim ::
    Set (SomeVariableName RewritingVariableName) ->
    Predicate RewritingVariableName ->
    Predicate RewritingVariableName
simplifyPredicateExistElim avoid predicate = case predicateF of
    Predicate.ExistsF existsF ->
        let existsF'@Exists.Exists{existsChild} = Exists.refreshExists avoid existsF
         in simplifyPredicateExistElim (avoid <> freeVariableNames existsF') existsChild
    _ -> predicate
  where
    _ :< predicateF = Recursive.project predicate

{- | Simplify a conjunction of predicates by simplifying each one
under the assumption that the others are true.
-}
simplifyPredicatesWithAssumptions ::
    SideCondition RewritingVariableName ->
    [Predicate RewritingVariableName] ->
    LogicT
        Simplifier
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
            (LogicT Simplifier)
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
        liftSimplifier (Predicate.simplify sideCondition' predicate) >>= Logic.scatter & lift

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
simplifyConjunctions original@(Predicate.toMultiAnd -> predicates) =
    case SideCondition.simplifyConjunctionByAssumption predicates of
        Unchanged _ -> Unchanged original
        Changed (changed, _) ->
            Changed (Predicate.fromMultiAnd changed)
