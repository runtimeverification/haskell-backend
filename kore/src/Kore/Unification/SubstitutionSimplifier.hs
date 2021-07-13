{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Unification.SubstitutionSimplifier (
    substitutionSimplifier,
    unificationMakeAnd,

    -- * Re-exports
    module Kore.Simplify.SubstitutionSimplifier,
) where

import Control.Error (
    MaybeT,
    maybeT,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrCondition (
    OrCondition,
 )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution (
    Normalization,
    Substitution,
 )
import Kore.Internal.TermLike (
    TermLike,
 )
import Kore.Log.DebugSubstitutionSimplifier (
    debugSubstitutionSimplifierResult,
    whileDebugSubstitutionSimplifier,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.AndTerms (
    termUnification,
 )
import Kore.Simplify.NotSimplifier
import qualified Kore.Simplify.Simplify as Simplifier
import Kore.Simplify.SubstitutionSimplifier (
    MakeAnd (..),
    SubstitutionSimplifier (..),
    deduplicateSubstitution,
    simplifySubstitutionWorker,
 )
import qualified Kore.TopBottom as TopBottom
import Kore.Unification.Unify
import qualified Logic
import Prelude.Kore

{- | A 'SubstitutionSimplifier' to use during unification.

If multiple assignments to a single variable cannot be unified, this simplifier
uses 'Unifier.throwUnificationError'.
-}
substitutionSimplifier ::
    forall unifier.
    MonadUnify unifier =>
    NotSimplifier unifier ->
    SubstitutionSimplifier unifier
substitutionSimplifier notSimplifier =
    SubstitutionSimplifier wrapper
  where
    wrapper ::
        SideCondition RewritingVariableName ->
        Substitution RewritingVariableName ->
        unifier (OrCondition RewritingVariableName)
    wrapper sideCondition substitution =
        whileDebugSubstitutionSimplifier $ do
            (predicate, result) <-
                worker substitution
                    & maybeT empty return
            let condition = Condition.fromNormalizationSimplified result
            let condition' = Condition.fromPredicate predicate <> condition
                conditions = OrCondition.fromCondition condition'
            TopBottom.guardAgainstBottom conditions
            debugSubstitutionSimplifierResult
            return conditions
      where
        worker ::
            Substitution RewritingVariableName ->
            MaybeT
                unifier
                ( Predicate RewritingVariableName
                , Normalization RewritingVariableName
                )
        worker =
            simplifySubstitutionWorker
                sideCondition
                (unificationMakeAnd notSimplifier)

unificationMakeAnd ::
    forall unifier.
    MonadUnify unifier =>
    NotSimplifier unifier ->
    MakeAnd unifier
unificationMakeAnd notSimplifier =
    MakeAnd{makeAnd}
  where
    makeAnd ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        SideCondition RewritingVariableName ->
        unifier (Pattern RewritingVariableName)
    makeAnd termLike1 termLike2 sideCondition = do
        unified <- termUnification notSimplifier termLike1 termLike2
        Simplifier.simplifyCondition sideCondition unified
            & Logic.lowerLogicT
