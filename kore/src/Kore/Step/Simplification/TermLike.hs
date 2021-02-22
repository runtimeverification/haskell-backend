{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}

{-# LANGUAGE Strict #-}

module Kore.Step.Simplification.TermLike
    ( simplify
    ) where

import Prelude.Kore

import qualified Control.Lens.Combinators as Lens
import Control.Monad.Catch
    ( MonadThrow
    )
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive

import Kore.Attribute.Pattern.FreeVariables
    ( freeVariables
    )
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
    ( andCondition
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( mapVariables
    , toRepresentation
    )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import qualified Kore.Internal.Substitution as Substitution
    ( toMap
    )
import Kore.Internal.TermLike
    ( TermLike
    , TermLikeF (..)
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Simplification.And as And
    ( simplify
    )
import qualified Kore.Step.Simplification.Application as Application
    ( simplify
    )
import qualified Kore.Step.Simplification.Bottom as Bottom
    ( simplify
    )
import qualified Kore.Step.Simplification.Ceil as Ceil
    ( simplify
    )
import qualified Kore.Step.Simplification.Defined as Defined
    ( simplify
    )
import qualified Kore.Step.Simplification.DomainValue as DomainValue
    ( simplify
    )
import qualified Kore.Step.Simplification.Equals as Equals
    ( simplify
    )
import qualified Kore.Step.Simplification.Exists as Exists
    ( simplify
    )
import qualified Kore.Step.Simplification.Floor as Floor
    ( simplify
    )
import qualified Kore.Step.Simplification.Forall as Forall
    ( simplify
    )
import qualified Kore.Step.Simplification.Iff as Iff
    ( simplify
    )
import qualified Kore.Step.Simplification.Implies as Implies
    ( simplify
    )
import qualified Kore.Step.Simplification.In as In
    ( simplify
    )
import qualified Kore.Step.Simplification.Inhabitant as Inhabitant
    ( simplify
    )
import qualified Kore.Step.Simplification.Inj as Inj
    ( simplify
    )
import qualified Kore.Step.Simplification.InternalBool as InternalBool
    ( simplify
    )
import qualified Kore.Step.Simplification.InternalBytes as InternalBytes
    ( simplify
    )
import qualified Kore.Step.Simplification.InternalInt as InternalInt
    ( simplify
    )
import qualified Kore.Step.Simplification.InternalList as InternalList
    ( simplify
    )
import qualified Kore.Step.Simplification.InternalMap as InternalMap
    ( simplify
    )
import qualified Kore.Step.Simplification.InternalSet as InternalSet
    ( simplify
    )
import qualified Kore.Step.Simplification.InternalString as InternalString
    ( simplify
    )
import qualified Kore.Step.Simplification.Mu as Mu
    ( simplify
    )
import qualified Kore.Step.Simplification.Next as Next
    ( simplify
    )
import qualified Kore.Step.Simplification.Not as Not
    ( notSimplifier
    , simplify
    )
import qualified Kore.Step.Simplification.Nu as Nu
    ( simplify
    )
import qualified Kore.Step.Simplification.Or as Or
    ( simplify
    )
import qualified Kore.Step.Simplification.Rewrites as Rewrites
    ( simplify
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.StringLiteral as StringLiteral
    ( simplify
    )
import qualified Kore.Step.Simplification.Top as Top
    ( simplify
    )
import qualified Kore.Step.Simplification.Variable as Variable
    ( simplify
    )
import Kore.Syntax.Variable
    ( AdjSomeVariableName (..)
    , ElementVariableName (..)
    , SetVariableName (..)
    , Variable (..)
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( unparse
    )
import qualified Kore.Variables.Binding as Binding
import Kore.Variables.Target
    ( Target (..)
    , targetIfEqual
    , unTarget
    )
import qualified Logic
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{- | Simplify 'TermLike' pattern to a disjunction of function-like 'Pattern's.
    All the resulting terms and conditions will be fully simplified, because after
    the term simplification procedure, the condition simplifier will be called as well.
 -}
simplify
    :: forall variable simplifier
    .  HasCallStack
    => InternalVariable variable
    => MonadSimplify simplifier
    => MonadThrow simplifier
    => SideCondition variable
    -> TermLike variable
    -> simplifier (OrPattern variable)
simplify sideCondition = \termLike ->
    simplifyInternalWorker termLike
    >>= ensureSimplifiedResult sideConditionRepresentation termLike
  where
    sideConditionRepresentation = SideCondition.toRepresentation sideCondition

    simplifyChildren
        :: Traversable t
        => t (TermLike variable)
        -> simplifier (t (OrPattern variable))
    simplifyChildren = traverse (simplifyTermLike sideCondition)

    simplifyInternalWorker
        :: TermLike variable -> simplifier (OrPattern variable)
    simplifyInternalWorker termLike
      | TermLike.isSimplified sideConditionRepresentation termLike =
        case Predicate.makePredicate termLike of
            Left _ -> return . OrPattern.fromTermLike $ termLike
            Right termPredicate -> do
                condition <-
                    ensureSimplifiedCondition
                        sideConditionRepresentation
                        termLike
                        (Condition.fromPredicate termPredicate)
                condition
                    & Pattern.fromCondition (termLikeSort termLike)
                    & OrPattern.fromPattern
                    & pure
      | otherwise =
        assertTermNotPredicate $ do
            unfixedTermOr <- descendAndSimplify termLike
            let termOr = OrPattern.coerceSort
                    (termLikeSort termLike)
                    unfixedTermOr
            returnIfSimplifiedOrContinue
                termLike
                (OrPattern.toPatterns termOr)
                (do
                    termPredicateList <- Logic.observeAllT $ do
                        termOrElement <- Logic.scatter termOr
                        simplified <-
                            simplifyCondition sideCondition termOrElement
                        return (applyTermSubstitution simplified)

                    returnIfSimplifiedOrContinue
                        termLike
                        termPredicateList
                        (do
                            resultsList <- mapM resimplify termPredicateList
                            return (MultiOr.mergeAll resultsList)
                        )
                )
      where

        resimplify :: Pattern variable -> simplifier (OrPattern variable)
        resimplify result = do
            let (resultTerm, resultPredicate) = Pattern.splitTerm result
            simplified <- simplifyInternalWorker resultTerm
            return (MultiOr.map (`Conditional.andCondition` resultPredicate) simplified)

        applyTermSubstitution :: Pattern variable -> Pattern variable
        applyTermSubstitution
            Conditional {term = term', predicate = predicate', substitution}
          =
            Conditional
                { term =
                    TermLike.substitute (Substitution.toMap substitution) term'
                , predicate = predicate'
                , substitution
                }

        assertTermNotPredicate getResults = do
            results <- getResults
            let
                -- The term of a result should never be any predicate other than
                -- Top or Bottom.
                hasPredicateTerm Conditional { term = term' }
                  | isTop term' || isBottom term' = False
                  | otherwise                     = Predicate.isPredicate term'
                unsimplified =
                    filter hasPredicateTerm $ OrPattern.toPatterns results
            if null unsimplified
                then return results
                else (error . show . Pretty.vsep)
                    [ "Incomplete simplification!"
                    , Pretty.indent 2 "input:"
                    , Pretty.indent 4 (unparse termLike)
                    , Pretty.indent 2 "unsimplified results:"
                    , (Pretty.indent 4 . Pretty.vsep)
                        (unparse <$> unsimplified)
                    , "Expected all predicates to be removed from the term."
                    ]

        returnIfSimplifiedOrContinue
            :: TermLike variable
            -> [Pattern variable]
            -> simplifier (OrPattern variable)
            -> simplifier (OrPattern variable)
        returnIfSimplifiedOrContinue originalTerm resultList continuation =
            case resultList of
                [] -> return OrPattern.bottom
                [result] ->
                    returnIfResultSimplifiedOrContinue
                        originalTerm result continuation
                _ -> continuation

        returnIfResultSimplifiedOrContinue
            :: TermLike variable
            -> Pattern variable
            -> simplifier (OrPattern variable)
            -> simplifier (OrPattern variable)
        returnIfResultSimplifiedOrContinue originalTerm result continuation
          | Pattern.isSimplified sideConditionRepresentation result
            && isTop resultTerm
            && resultSubstitutionIsEmpty
          = return (OrPattern.fromPattern result)
          | Pattern.isSimplified sideConditionRepresentation result
            && isTop resultPredicate
          = return (OrPattern.fromPattern result)
          | isTop resultPredicate && resultTerm == originalTerm
          = return
                (OrPattern.fromTermLike
                    (TermLike.markSimplifiedConditional
                        sideConditionRepresentation
                        resultTerm
                    )
                )
          | isTop resultTerm
          , Right condition <- termAsPredicate
          , resultPredicate == condition
          = return
                $ OrPattern.fromPattern
                $ Pattern.fromCondition_
                $ Condition.markPredicateSimplifiedConditional
                    sideConditionRepresentation
                    resultPredicate
          | otherwise = continuation
          where
            (resultTerm, resultPredicate) = Pattern.splitTerm result
            resultSubstitutionIsEmpty =
                case resultPredicate of
                    Conditional {substitution} -> substitution == mempty
            termAsPredicate =
                Condition.fromPredicate <$> Predicate.makePredicate originalTerm

    descendAndSimplify :: TermLike variable -> simplifier (OrPattern variable)
    descendAndSimplify termLike =
        let ~doNotSimplify =
                assert
                    (TermLike.isSimplified sideConditionRepresentation termLike)
                return (OrPattern.fromTermLike termLike)
            avoiding = freeVariables termLike <> freeVariables sideCondition
            refreshElementBinder = TermLike.refreshElementBinder avoiding
            refreshSetBinder = TermLike.refreshSetBinder avoiding
            (_ :< termLikeF) = Recursive.project termLike
        in case termLikeF of
            -- Unimplemented cases
            ApplyAliasF _ -> doNotSimplify
            -- Do not simplify non-simplifiable patterns.
            EvaluatedF  _ -> doNotSimplify
            EndiannessF _ -> doNotSimplify
            SignednessF _ -> doNotSimplify
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
            CeilF ceilF ->
                Ceil.simplify sideCondition =<< simplifyChildren ceilF
            EqualsF equalsF ->
                Equals.simplify sideCondition =<< simplifyChildren equalsF
            ExistsF exists -> do
                simplifiedChildren <-
                    simplifyChildren (refresh exists)
                targetedResults <-
                    Exists.simplify
                        (targetSideCondition sideCondition)
                        (targetSimplifiedChildren simplifiedChildren)
                let unTargetedResults =
                        MultiOr.map (Pattern.mapVariables (pure unTarget)) targetedResults
                return unTargetedResults
              where
                refresh = Lens.over Binding.existsBinder refreshElementBinder
                targetSideCondition
                    :: SideCondition variable
                    -> SideCondition (Target variable)
                targetSideCondition =
                    SideCondition.mapVariables
                        AdjSomeVariableName
                        { adjSomeVariableNameElement =
                            ElementVariableName
                            (targetIfEqual existsVariableName)
                        , adjSomeVariableNameSet = SetVariableName NonTarget
                        }
                targetSimplifiedChildren
                    :: TermLike.Exists
                        TermLike.Sort
                        variable
                        (OrPattern variable)
                    -> TermLike.Exists
                        TermLike.Sort
                        (Target variable)
                        (OrPattern (Target variable))
                targetSimplifiedChildren =
                    Lens.over Binding.existsBinder OrPattern.targetBinder
                existsVariableName =
                    (unElementVariableName . variableName)
                        (TermLike.existsVariable exists)
            IffF iffF ->
                Iff.simplify sideCondition =<< simplifyChildren iffF
            ImpliesF impliesF ->
                Implies.simplify sideCondition =<< simplifyChildren impliesF
            InF inF ->
                In.simplify sideCondition =<< simplifyChildren inF
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
            RewritesF rewritesF ->
                Rewrites.simplify <$> simplifyChildren rewritesF
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
            DefinedF definedF ->
                Defined.simplify <$> simplifyChildren definedF

ensureSimplifiedResult
    :: InternalVariable variable
    => Monad simplifier
    => SideCondition.Representation
    -> TermLike variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
ensureSimplifiedResult repr termLike results
  | OrPattern.isSimplified repr results = pure results
      -- trace
      --     ("\nIs simplified:\n" <> unlines (unparseToString <$> toList results)
      --     <> "\nWith side cond:\n" <> (show . Pretty.pretty) repr
      --     )
      --     $ pure results
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

ensureSimplifiedCondition
    :: InternalVariable variable
    => Monad simplifier
    => SideCondition.Representation
    -> TermLike variable
    -> Condition variable
    -> simplifier (Condition variable)
ensureSimplifiedCondition repr termLike condition
  | Condition.isSimplified repr condition = pure condition
  | otherwise =
    (error . show . Pretty.vsep)
        [ "Internal error: expected simplified condition, but found:"
        , Pretty.indent 4 (pretty condition)
        , Pretty.indent 2 "while simplifying:"
        , Pretty.indent 4 (unparse termLike)
        ]
