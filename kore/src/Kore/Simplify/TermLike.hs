{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.TermLike (
    simplify,
) where

import Control.Lens.Combinators qualified as Lens
import Control.Monad.Catch (
    MonadThrow,
 )
import Data.Functor.Const
import Data.Functor.Foldable qualified as Recursive
import Kore.Attribute.Pattern.FreeVariables (
    freeVariableNames,
    freeVariables,
 )
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.From
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.TermLike (
    TermLike,
    TermLikeF (..),
    termLikeSort,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.And qualified as And (
    simplify,
 )
import Kore.Simplify.Application qualified as Application (
    simplify,
 )
import Kore.Simplify.DomainValue qualified as DomainValue (
    simplify,
 )
import Kore.Simplify.Exists qualified as Exists (
    simplify,
 )
import Kore.Simplify.Forall qualified as Forall (
    simplify,
 )
import Kore.Simplify.Iff qualified as Iff (
    simplify,
 )
import Kore.Simplify.Implies qualified as Implies (
    simplify,
 )
import Kore.Simplify.Inhabitant qualified as Inhabitant (
    simplify,
 )
import Kore.Simplify.Inj qualified as Inj (
    simplify,
 )
import Kore.Simplify.InternalBool qualified as InternalBool (
    simplify,
 )
import Kore.Simplify.InternalBytes qualified as InternalBytes (
    simplify,
 )
import Kore.Simplify.InternalInt qualified as InternalInt (
    simplify,
 )
import Kore.Simplify.InternalList qualified as InternalList (
    simplify,
 )
import Kore.Simplify.InternalMap qualified as InternalMap (
    simplify,
 )
import Kore.Simplify.InternalSet qualified as InternalSet (
    simplify,
 )
import Kore.Simplify.InternalString qualified as InternalString (
    simplify,
 )
import Kore.Simplify.Mu qualified as Mu (
    simplify,
 )
import Kore.Simplify.Next qualified as Next (
    simplify,
 )
import Kore.Simplify.Not qualified as Not (
    notSimplifier,
    simplify,
 )
import Kore.Simplify.Nu qualified as Nu (
    simplify,
 )
import Kore.Simplify.Or qualified as Or (
    simplify,
 )
import Kore.Simplify.Simplify
import Kore.Simplify.StringLiteral qualified as StringLiteral (
    simplify,
 )
import Kore.Simplify.Variable qualified as Variable (
    simplify,
 )
import Kore.Syntax (
    Ceil (..),
    Equals (..),
    Floor (..),
    In (..),
    refreshExists,
    refreshForall,
 )
import Kore.Variables.Binding qualified as Binding
import Prelude.Kore

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

-- | Simplify the given 'TermLike'. Do not simplify any side conditions.
simplify ::
    forall simplifier.
    MonadSimplify simplifier =>
    MonadThrow simplifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplify sideCondition =
    loop . OrPattern.fromTermLike
  where
    loop ::
        OrPattern RewritingVariableName ->
        simplifier (OrPattern RewritingVariableName)
    loop input = do
        output <- MultiOr.traverseOr (propagateConditions worker) input
        if input == output
            then pure output
            else loop output

    replaceTerm = SideCondition.replaceTerm sideCondition

    repr = SideCondition.toRepresentation sideCondition

    propagateConditions action input = do
        results <- action (Conditional.term input)
        MultiOr.map (input *>) results
            & return
    {-# INLINE propagateConditions #-}

    worker ::
        TermLike RewritingVariableName ->
        simplifier (OrPattern RewritingVariableName)
    worker termLike
        | Just termLike' <- replaceTerm termLike =
            worker termLike'
        | TermLike.isSimplified repr termLike =
            pure (OrPattern.fromTermLike termLike)
        | otherwise =
            case termLikeF of
                -- Not implemented:
                ApplyAliasF _ -> doNotSimplify
                -- Not simplifiable:
                EndiannessF _ -> doNotSimplify
                SignednessF _ -> doNotSimplify
                -- Handled elsewhere, not a proper term:
                RewritesF _ -> doNotSimplify
                -- Symbols:
                ApplySymbolF applySymbolF ->
                    Application.simplify sideCondition
                        =<< traverse worker applySymbolF
                InjF injF ->
                    Inj.simplify =<< traverse worker injF
                InternalListF internalListF ->
                    InternalList.simplify <$> traverse worker internalListF
                InternalMapF internalMapF ->
                    InternalMap.simplify <$> traverse worker internalMapF
                InternalSetF internalSetF ->
                    InternalSet.simplify <$> traverse worker internalSetF
                -- Domain values:
                DomainValueF domainValueF ->
                    DomainValue.simplify <$> traverse worker domainValueF
                InternalBoolF internalBoolF ->
                    InternalBool.simplify (getConst internalBoolF)
                        & return
                InternalBytesF internalBytesF ->
                    InternalBytes.simplify (getConst internalBytesF)
                        & return
                InternalIntF internalIntF ->
                    InternalInt.simplify (getConst internalIntF)
                        & return
                InternalStringF internalStringF ->
                    InternalString.simplify (getConst internalStringF)
                        & return
                -- Reachability:
                NextF nextF ->
                    Next.simplify <$> traverse worker nextF
                -- Matching Logic:
                AndF andF -> do
                    let conjuncts = foldMap MultiAnd.fromTermLike andF
                    -- MultiAnd doesn't preserve the sort so we need to send it as an external argument
                    And.simplify sort Not.notSimplifier sideCondition
                        =<< MultiAnd.traverse worker conjuncts
                OrF orF ->
                    Or.simplify <$> traverse worker orF
                NotF notF ->
                    Not.simplify sideCondition
                        =<< traverse worker notF
                ImpliesF impliesF ->
                    Implies.simplify sideCondition
                        =<< traverse worker impliesF
                IffF iffF ->
                    Iff.simplify sideCondition
                        =<< traverse worker iffF
                InhabitantF inhF ->
                    Inhabitant.simplify <$> traverse worker inhF
                -- Binders:
                ExistsF existsF ->
                    Exists.simplify sideCondition
                        =<< traverse worker (refresh existsF)
                  where
                    avoid =
                        freeVariableNames termLike
                            <> freeVariableNames sideCondition
                    refresh = refreshExists avoid
                ForallF forallF ->
                    Forall.simplify <$> traverse worker (refresh forallF)
                  where
                    avoid =
                        freeVariableNames termLike
                            <> freeVariableNames sideCondition
                    refresh = refreshForall avoid
                MuF muF ->
                    Mu.simplify <$> traverse worker (refreshMu muF)
                NuF nuF ->
                    Nu.simplify <$> traverse worker (refreshNu nuF)
                VariableF variableF ->
                    Variable.simplify (getConst variableF)
                        & return
                StringLiteralF stringLiteralF ->
                    StringLiteral.simplify (getConst stringLiteralF)
                        & return
                -- Predicates:
                -- (Predicates are not simplified because this function
                -- doesn't simplify side conditions.)
                TopF _ ->
                    returnPredicate fromTop_
                BottomF _ ->
                    returnPredicate fromBottom_
                CeilF Ceil{ceilChild} ->
                    returnPredicate (fromCeil_ ceilChild)
                FloorF Floor{floorChild} ->
                    returnPredicate (fromFloor_ floorChild)
                EqualsF Equals{equalsFirst, equalsSecond} ->
                    returnPredicate (fromEquals_ equalsFirst equalsSecond)
                InF In{inContainedChild, inContainingChild} ->
                    returnPredicate
                        (fromIn_ inContainedChild inContainingChild)
      where
        _ :< termLikeF = Recursive.project termLike
        ~sort = termLikeSort termLike

        ~doNotSimplify = return (OrPattern.fromTermLike termLike)

        ~avoiding = freeVariables termLike <> freeVariables sideCondition
        refreshSetBinder = TermLike.refreshSetBinder avoiding
        refreshMu = Lens.over Binding.muBinder refreshSetBinder
        refreshNu = Lens.over Binding.nuBinder refreshSetBinder

        returnPredicate =
            Pattern.fromPredicateSorted sort
                >>> OrPattern.fromPattern
                >>> return
