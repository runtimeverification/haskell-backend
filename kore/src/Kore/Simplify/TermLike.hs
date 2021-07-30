{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.TermLike (
    simplify,
) where

import qualified Control.Lens.Combinators as Lens
import Control.Monad.Catch (
    MonadThrow,
 )
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import Kore.Attribute.Pattern.FreeVariables (
    freeVariableNames,
    freeVariables,
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.From
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike (
    TermLike,
    TermLikeF (..),
    termLikeSort,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.And as And (
    simplify,
 )
import qualified Kore.Simplify.Application as Application (
    simplify,
 )
import qualified Kore.Simplify.DomainValue as DomainValue (
    simplify,
 )
import qualified Kore.Simplify.Exists as Exists (
    simplify,
 )
import qualified Kore.Simplify.Forall as Forall (
    simplify,
 )
import qualified Kore.Simplify.Iff as Iff (
    simplify,
 )
import qualified Kore.Simplify.Implies as Implies (
    simplify,
 )
import qualified Kore.Simplify.Inhabitant as Inhabitant (
    simplify,
 )
import qualified Kore.Simplify.Inj as Inj (
    simplify,
 )
import qualified Kore.Simplify.InternalBool as InternalBool (
    simplify,
 )
import qualified Kore.Simplify.InternalBytes as InternalBytes (
    simplify,
 )
import qualified Kore.Simplify.InternalInt as InternalInt (
    simplify,
 )
import qualified Kore.Simplify.InternalList as InternalList (
    simplify,
 )
import qualified Kore.Simplify.InternalMap as InternalMap (
    simplify,
 )
import qualified Kore.Simplify.InternalSet as InternalSet (
    simplify,
 )
import qualified Kore.Simplify.InternalString as InternalString (
    simplify,
 )
import qualified Kore.Simplify.Mu as Mu (
    simplify,
 )
import qualified Kore.Simplify.Next as Next (
    simplify,
 )
import qualified Kore.Simplify.Not as Not (
    notSimplifier,
    simplify,
 )
import qualified Kore.Simplify.Nu as Nu (
    simplify,
 )
import qualified Kore.Simplify.Or as Or (
    simplify,
 )
import Kore.Simplify.Simplify
import qualified Kore.Simplify.StringLiteral as StringLiteral (
    simplify,
 )
import qualified Kore.Simplify.Variable as Variable (
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
import qualified Kore.Variables.Binding as Binding
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
    loop 0 . OrPattern.fromTermLike
  where
    limit :: Int
    limit = 4

    loop ::
        Int ->
        OrPattern RewritingVariableName ->
        simplifier (OrPattern RewritingVariableName)
    loop count input
        | count >= limit =
            trace "\nexceeded term simplifier limit\n" $
                pure input
        | otherwise = do
            output <- MultiOr.traverseOr (propagateConditions worker) input
            if input == output
                then pure output -- (OrPattern.markTermSimplifiedConditionally repr output)
                else loop (count + 1) output

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
                    And.simplify Not.notSimplifier sideCondition
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
