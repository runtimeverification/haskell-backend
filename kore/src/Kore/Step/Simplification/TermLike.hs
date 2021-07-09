{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.TermLike (
    simplify,
    simplifyOnly,
) where

import qualified Control.Lens.Combinators as Lens
import Control.Monad.Catch (
    MonadThrow,
 )
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import Kore.Attribute.Pattern.FreeVariables (
    freeVariables,
 )
import Kore.Internal.Condition (
    Condition,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.From
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    Representation,
 )
import qualified Kore.Internal.Substitution as Substitution (
    toMap,
 )
import Kore.Internal.TermLike (
    TermLike,
    TermLikeF (..),
    termLikeSort,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.Simplification.And as And (
    simplify,
 )
import qualified Kore.Step.Simplification.Application as Application (
    simplify,
 )
import qualified Kore.Step.Simplification.Bottom as Bottom (
    simplify,
 )
import qualified Kore.Step.Simplification.Ceil as Ceil (
    simplify,
 )
import qualified Kore.Step.Simplification.DomainValue as DomainValue (
    simplify,
 )
import qualified Kore.Step.Simplification.Equals as Equals (
    simplify,
 )
import qualified Kore.Step.Simplification.Exists as Exists (
    simplify,
 )
import qualified Kore.Step.Simplification.Floor as Floor (
    simplify,
 )
import qualified Kore.Step.Simplification.Forall as Forall (
    simplify,
 )
import qualified Kore.Step.Simplification.Iff as Iff (
    simplify,
 )
import qualified Kore.Step.Simplification.Implies as Implies (
    simplify,
 )
import qualified Kore.Step.Simplification.In as In (
    simplify,
 )
import qualified Kore.Step.Simplification.Inhabitant as Inhabitant (
    simplify,
 )
import qualified Kore.Step.Simplification.Inj as Inj (
    simplify,
 )
import qualified Kore.Step.Simplification.InternalBool as InternalBool (
    simplify,
 )
import qualified Kore.Step.Simplification.InternalBytes as InternalBytes (
    simplify,
 )
import qualified Kore.Step.Simplification.InternalInt as InternalInt (
    simplify,
 )
import qualified Kore.Step.Simplification.InternalList as InternalList (
    simplify,
 )
import qualified Kore.Step.Simplification.InternalMap as InternalMap (
    simplify,
 )
import qualified Kore.Step.Simplification.InternalSet as InternalSet (
    simplify,
 )
import qualified Kore.Step.Simplification.InternalString as InternalString (
    simplify,
 )
import qualified Kore.Step.Simplification.Mu as Mu (
    simplify,
 )
import qualified Kore.Step.Simplification.Next as Next (
    simplify,
 )
import qualified Kore.Step.Simplification.Not as Not (
    notSimplifier,
    simplify,
 )
import qualified Kore.Step.Simplification.Nu as Nu (
    simplify,
 )
import qualified Kore.Step.Simplification.Or as Or (
    simplify,
 )
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.StringLiteral as StringLiteral (
    simplify,
 )
import qualified Kore.Step.Simplification.Top as Top (
    simplify,
 )
import qualified Kore.Step.Simplification.Variable as Variable (
    simplify,
 )
import Kore.Substitute
import Kore.Syntax (
    Ceil (..),
    Equals (..),
    Floor (..),
    In (..),
 )
import Kore.TopBottom (
    TopBottom (..),
 )
import Kore.Unparser (
    unparse,
 )
import qualified Kore.Variables.Binding as Binding
import qualified Logic
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{- | Simplify 'TermLike' pattern to a disjunction of function-like 'Pattern's.
    All the resulting terms and conditions will be fully simplified, because after
    the term simplification procedure, the condition simplifier will be called as well.
-}
simplify ::
    forall simplifier.
    HasCallStack =>
    MonadSimplify simplifier =>
    MonadThrow simplifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplify sideCondition = \termLike ->
    simplifyInternalWorker termLike
        >>= ensureSimplifiedResult sideConditionRepresentation termLike
  where
    sideConditionRepresentation = SideCondition.toRepresentation sideCondition

    simplifyChildren ::
        Traversable t =>
        t (TermLike RewritingVariableName) ->
        simplifier (t (OrPattern RewritingVariableName))
    simplifyChildren = traverse (simplifyTermLike sideCondition)

    simplifyInternalWorker ::
        TermLike RewritingVariableName ->
        simplifier (OrPattern RewritingVariableName)
    simplifyInternalWorker termLike
        | Just termLike' <- continueSimplificationWith termLike =
            assertTermNotPredicate $ do
                unfixedTermOr <- descendAndSimplify termLike'
                let termOr =
                        OrPattern.coerceSort
                            (termLikeSort termLike')
                            unfixedTermOr
                returnIfSimplifiedOrContinue
                    termLike'
                    (OrPattern.toPatterns termOr)
                    ( do
                        termPredicateList <- Logic.observeAllT $ do
                            termOrElement <- Logic.scatter termOr
                            simplified <-
                                simplifyCondition sideCondition termOrElement
                            return (applyTermSubstitution simplified)

                        returnIfSimplifiedOrContinue
                            termLike'
                            termPredicateList
                            ( do
                                resultsList <- mapM resimplify termPredicateList
                                return (MultiOr.mergeAll resultsList)
                            )
                    )
        | otherwise =
            case Predicate.makePredicate termLike of
                Left _ -> return . OrPattern.fromTermLike $ termLike
                Right predicate -> do
                    condition <-
                        Condition.fromPredicate predicate
                            & ensureSimplifiedCondition
                                sideConditionRepresentation
                                termLike
                    condition
                        & Pattern.fromCondition (termLikeSort termLike)
                        & OrPattern.fromPattern
                        & pure
      where
        continueSimplificationWith ::
            TermLike RewritingVariableName ->
            Maybe (TermLike RewritingVariableName)
        continueSimplificationWith original =
            let isOriginalNotSimplified
                    | TermLike.isSimplified sideConditionRepresentation original =
                        Nothing
                    | otherwise = Just original
             in SideCondition.replaceTerm sideCondition original
                    <|> isOriginalNotSimplified

        resimplify ::
            Pattern RewritingVariableName ->
            simplifier (OrPattern RewritingVariableName)
        resimplify result = do
            let (resultTerm, resultPredicate) = Pattern.splitTerm result
            simplified <- simplifyInternalWorker resultTerm
            return
                ( MultiOr.map
                    (`Conditional.andCondition` resultPredicate)
                    simplified
                )

        applyTermSubstitution ::
            InternalVariable variable =>
            Pattern variable ->
            Pattern variable
        applyTermSubstitution conditional@Conditional{substitution} =
            fmap (substitute (Substitution.toMap substitution)) conditional

        assertTermNotPredicate getResults = do
            results <- getResults
            let -- The term of a result should never be any predicate other than
                -- Top or Bottom.
                hasPredicateTerm Conditional{term = term'}
                    | isTop term' || isBottom term' = False
                    | otherwise = Predicate.isPredicate term'
                unsimplified =
                    filter hasPredicateTerm $ OrPattern.toPatterns results
            if null unsimplified
                then return results
                else
                    (error . show . Pretty.vsep)
                        [ "Incomplete simplification!"
                        , Pretty.indent 2 "input:"
                        , Pretty.indent 4 (unparse termLike)
                        , Pretty.indent 2 "unsimplified results:"
                        , (Pretty.indent 4 . Pretty.vsep)
                            (unparse <$> unsimplified)
                        , "Expected all predicates to be removed from the term."
                        ]

        returnIfSimplifiedOrContinue ::
            TermLike RewritingVariableName ->
            [Pattern RewritingVariableName] ->
            simplifier (OrPattern RewritingVariableName) ->
            simplifier (OrPattern RewritingVariableName)
        returnIfSimplifiedOrContinue originalTerm resultList continuation =
            case resultList of
                [] -> return OrPattern.bottom
                [result] ->
                    returnIfResultSimplifiedOrContinue
                        originalTerm
                        result
                        continuation
                _ -> continuation

        returnIfResultSimplifiedOrContinue ::
            TermLike RewritingVariableName ->
            Pattern RewritingVariableName ->
            simplifier (OrPattern RewritingVariableName) ->
            simplifier (OrPattern RewritingVariableName)
        returnIfResultSimplifiedOrContinue originalTerm result continuation
            | Pattern.isSimplified sideConditionRepresentation result
              , isTop resultTerm
              , resultSubstitutionIsEmpty
              , SideCondition.cannotReplaceTerm sideCondition (Pattern.term result) =
                return (OrPattern.fromPattern result)
            | Pattern.isSimplified sideConditionRepresentation result
              , isTop resultPredicate
              , SideCondition.cannotReplaceTerm sideCondition (Pattern.term result) =
                return (OrPattern.fromPattern result)
            | isTop resultPredicate && resultTerm == originalTerm
              , SideCondition.cannotReplaceTerm sideCondition (Pattern.term result) =
                return
                    ( OrPattern.fromTermLike
                        ( TermLike.markSimplifiedConditional
                            sideConditionRepresentation
                            resultTerm
                        )
                    )
            | isTop resultTerm
              , Right condition <- termAsPredicate
              , resultPredicate == condition =
                return $
                    OrPattern.fromPattern $
                        Pattern.fromCondition_ $
                            Condition.markPredicateSimplifiedConditional
                                sideConditionRepresentation
                                resultPredicate
            | otherwise = continuation
          where
            (resultTerm, resultPredicate) = Pattern.splitTerm result
            resultSubstitutionIsEmpty =
                case resultPredicate of
                    Conditional{substitution} -> substitution == mempty
            termAsPredicate =
                Condition.fromPredicate <$> Predicate.makePredicate originalTerm

    descendAndSimplify ::
        TermLike RewritingVariableName ->
        simplifier (OrPattern RewritingVariableName)
    descendAndSimplify termLike =
        let ~doNotSimplify =
                assert
                    (TermLike.isSimplified sideConditionRepresentation termLike)
                    return
                    (OrPattern.fromTermLike termLike)
            avoiding = freeVariables termLike <> freeVariables sideCondition
            refreshElementBinder = TermLike.refreshElementBinder avoiding
            refreshSetBinder = TermLike.refreshSetBinder avoiding
            ~sort = termLikeSort termLike
            (_ :< termLikeF) = Recursive.project termLike
         in case termLikeF of
                -- Unimplemented cases
                ApplyAliasF _ -> doNotSimplify
                -- Do not simplify non-simplifiable patterns.
                EndiannessF _ -> doNotSimplify
                SignednessF _ -> doNotSimplify
                -- We should never attempt to simplify a Rewrites term as this is only used for rules parsing.
                RewritesF _ -> error "Attempting to simplify a Rewrites term. This is an error. Please report it at https://github.com/kframework/kore/issues"
                --
                AndF andF -> do
                    let conjuncts = foldMap MultiAnd.fromTermLike andF
                    And.simplify Not.notSimplifier sideCondition
                        =<< MultiAnd.traverse
                            (simplifyTermLike sideCondition)
                            conjuncts
                ApplySymbolF applySymbolF ->
                    Application.simplify sideCondition
                        =<< simplifyChildren applySymbolF
                InjF injF ->
                    Inj.simplify =<< simplifyChildren injF
                CeilF ceilF -> do
                    ceilF' <- simplifyChildren ceilF
                    conditions <- Ceil.simplify sideCondition ceilF'
                    pure (OrPattern.fromOrCondition sort conditions)
                EqualsF equalsF -> do
                    equalsF' <- simplifyChildren equalsF
                    conditions <- Equals.simplify sideCondition equalsF'
                    pure (OrPattern.fromOrCondition sort conditions)
                ExistsF exists -> do
                    simplifiedChildren <-
                        simplifyChildren (refresh exists)
                    Exists.simplify sideCondition simplifiedChildren
                  where
                    refresh = Lens.over Binding.existsBinder refreshElementBinder
                IffF iffF ->
                    Iff.simplify sideCondition =<< simplifyChildren iffF
                ImpliesF impliesF ->
                    Implies.simplify sideCondition =<< simplifyChildren impliesF
                InF inF -> do
                    inF' <- simplifyChildren inF
                    conditions <- In.simplify sideCondition inF'
                    pure (OrPattern.fromOrCondition sort conditions)
                NotF notF ->
                    Not.simplify sideCondition =<< simplifyChildren notF
                --
                BottomF bottomF ->
                    Bottom.simplify <$> simplifyChildren bottomF
                InternalListF internalF ->
                    InternalList.simplify <$> simplifyChildren internalF
                InternalMapF internalMapF ->
                    InternalMap.simplify <$> simplifyChildren internalMapF
                InternalSetF internalSetF ->
                    InternalSet.simplify <$> simplifyChildren internalSetF
                DomainValueF domainValueF ->
                    DomainValue.simplify <$> simplifyChildren domainValueF
                FloorF floorF -> Floor.simplify <$> simplifyChildren floorF
                ForallF forall ->
                    Forall.simplify <$> simplifyChildren (refresh forall)
                  where
                    refresh = Lens.over Binding.forallBinder refreshElementBinder
                InhabitantF inhF ->
                    Inhabitant.simplify <$> simplifyChildren inhF
                MuF mu ->
                    Mu.simplify <$> simplifyChildren (refresh mu)
                  where
                    refresh = Lens.over Binding.muBinder refreshSetBinder
                NuF nu ->
                    Nu.simplify <$> simplifyChildren (refresh nu)
                  where
                    refresh = Lens.over Binding.nuBinder refreshSetBinder
                -- TODO(virgil): Move next up through patterns.
                NextF nextF -> Next.simplify <$> simplifyChildren nextF
                OrF orF -> Or.simplify <$> simplifyChildren orF
                TopF topF -> Top.simplify <$> simplifyChildren topF
                --
                StringLiteralF stringLiteralF ->
                    return $ StringLiteral.simplify (getConst stringLiteralF)
                InternalBoolF internalBoolF ->
                    return $ InternalBool.simplify (getConst internalBoolF)
                InternalBytesF internalBytesF ->
                    return $ InternalBytes.simplify (getConst internalBytesF)
                InternalIntF internalIntF ->
                    return $ InternalInt.simplify (getConst internalIntF)
                InternalStringF internalStringF ->
                    return $ InternalString.simplify (getConst internalStringF)
                VariableF variableF ->
                    return $ Variable.simplify (getConst variableF)

{- | We expect each predicate in the result to have been fully
 simplified with a different side condition.
 See 'Kore.Step.Simplification.Condition.simplifyPredicates'.
-}
ensureSimplifiedResult ::
    Monad simplifier =>
    SideCondition.Representation ->
    TermLike RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
ensureSimplifiedResult repr termLike results
    | OrPattern.hasSimplifiedChildrenIgnoreConditions results =
        pure results
    | otherwise =
        (error . show . Pretty.vsep)
            [ "Internal error: expected simplified results, but found:"
            , (Pretty.indent 4 . Pretty.vsep)
                (unparse <$> OrPattern.toPatterns results)
            , Pretty.indent 2 "while simplifying:"
            , Pretty.indent 4 (unparse termLike)
            , Pretty.indent 2 "with side condition:"
            , Pretty.indent 4 (Pretty.pretty repr)
            ]

ensureSimplifiedCondition ::
    Monad simplifier =>
    SideCondition.Representation ->
    TermLike RewritingVariableName ->
    Condition RewritingVariableName ->
    simplifier (Condition RewritingVariableName)
ensureSimplifiedCondition repr termLike condition
    | Condition.isSimplified repr condition = pure condition
    | otherwise =
        (error . show . Pretty.vsep)
            [ "Internal error: expected simplified condition, but found:"
            , Pretty.indent 4 (pretty condition)
            , Pretty.indent 2 "while simplifying:"
            , Pretty.indent 4 (unparse termLike)
            ]

-- | Simplify the given 'TermLike'. Do not simplify any side conditions.
simplifyOnly ::
    forall simplifier.
    MonadSimplify simplifier =>
    MonadThrow simplifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyOnly sideCondition =
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
                        =<< traverse worker (refreshExists existsF)
                ForallF forallF ->
                    Forall.simplify <$> traverse worker (refreshForall forallF)
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
        refreshElementBinder = TermLike.refreshElementBinder avoiding
        refreshExists = Lens.over Binding.existsBinder refreshElementBinder
        refreshForall = Lens.over Binding.forallBinder refreshElementBinder
        refreshSetBinder = TermLike.refreshSetBinder avoiding
        refreshMu = Lens.over Binding.muBinder refreshSetBinder
        refreshNu = Lens.over Binding.nuBinder refreshSetBinder

        returnPredicate =
            Pattern.fromPredicateSorted sort
                >>> OrPattern.fromPattern
                >>> return
