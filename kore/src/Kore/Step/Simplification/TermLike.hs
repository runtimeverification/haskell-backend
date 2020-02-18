{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.TermLike
    ( simplify
    , simplifyToOr
    , simplifyInternal
    ) where

import Prelude.Kore

import Control.Comonad.Trans.Cofree
    ( CofreeF ((:<))
    )
import qualified Control.Lens.Combinators as Lens
import Control.Monad
    ( unless
    )
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Branch as BranchT
    ( gather
    , scatter
    )
import Kore.Attribute.Pattern.FreeVariables
    ( freeVariables
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
    ( andCondition
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( mapVariables
    , toRepresentation
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
import qualified Kore.Profiler.Profile as Profiler
    ( identifierSimplification
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( matchAxiomIdentifier
    )
import qualified Kore.Step.Simplification.And as And
    ( simplify
    )
import qualified Kore.Step.Simplification.Application as Application
    ( simplify
    )
import qualified Kore.Step.Simplification.Bottom as Bottom
    ( simplify
    )
import qualified Kore.Step.Simplification.Builtin as Builtin
    ( simplify
    )
import qualified Kore.Step.Simplification.Ceil as Ceil
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
import qualified Kore.Step.Simplification.InternalBytes as InternalBytes
    ( simplify
    )
import qualified Kore.Step.Simplification.Mu as Mu
    ( simplify
    )
import qualified Kore.Step.Simplification.Next as Next
    ( simplify
    )
import qualified Kore.Step.Simplification.Not as Not
    ( simplify
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
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( unparse
    , unparseToString
    )
import qualified Kore.Variables.Binding as Binding
import Kore.Variables.Target
    ( Target (..)
    , mkSetNonTarget
    , targetIfEqual
    , unTargetElement
    , unTargetSet
    )

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{-|'simplify' simplifies a `TermLike`, returning a 'Pattern'.
-}
simplify
    ::  ( HasCallStack
        , InternalVariable variable
        , MonadSimplify simplifier
        )
    =>  TermLike variable
    ->  SideCondition variable
    ->  simplifier (Pattern variable)
simplify patt sideCondition = do
    orPatt <- simplifyToOr sideCondition patt
    return (OrPattern.toPattern orPatt)

{-|'simplifyToOr' simplifies a TermLike variable, returning an
'OrPattern'.
-}
simplifyToOr
    ::  ( HasCallStack
        , InternalVariable variable
        , MonadSimplify simplifier
        )
    =>  SideCondition variable
    ->  TermLike variable
    ->  simplifier (OrPattern variable)
simplifyToOr sideCondition term =
    localSimplifierTermLike (const simplifier)
        . simplifyInternal term
        $ sideCondition
  where
    simplifier = termLikeSimplifier simplifyToOr

simplifyInternal
    ::  forall variable simplifier
    .   ( HasCallStack
        , InternalVariable variable
        , MonadSimplify simplifier
        )
    =>  TermLike variable
    ->  SideCondition variable
    ->  simplifier (OrPattern variable)
simplifyInternal term sideCondition = do
    result <- simplifyInternalWorker term
    unless
        (OrPattern.isSimplified
            (SideCondition.toRepresentation sideCondition)
            result
        )
        (error $ unlines
            (   [ "Not simplified."
                , "result = "
                ]
            ++ map unparseToString (OrPattern.toPatterns result)
            ++ map show (OrPattern.toPatterns result)
            )
        )
    return result
  where
    tracer termLike =
        maybe id Profiler.identifierSimplification
        $ AxiomIdentifier.matchAxiomIdentifier termLike

    simplifyChildren
        :: Traversable t
        => t (TermLike variable)
        -> simplifier (t (OrPattern variable))
    simplifyChildren = traverse simplifyInternalWorker

    assertConditionSimplified
        :: TermLike variable -> Condition variable -> Condition variable
    assertConditionSimplified originalTerm condition =
        if Condition.isSimplified sideConditionRepresentation condition
            then condition
            else (error . unlines)
                [ "Not simplified."
                , "term = "
                , unparseToString originalTerm
                , "condition = "
                , unparseToString condition
                ]

    simplifyInternalWorker
        :: TermLike variable -> simplifier (OrPattern variable)
    simplifyInternalWorker termLike
        | TermLike.isSimplified sideConditionRepresentation termLike
        = case Predicate.makePredicate termLike of
            Left _ -> return . OrPattern.fromTermLike $ termLike
            Right termPredicate ->
                return
                $ OrPattern.fromPattern
                $ Pattern.fromConditionSorted (termLikeSort termLike)
                $ assertConditionSimplified termLike
                $ Condition.fromPredicate termPredicate
        | otherwise
        = assertTermNotPredicate $ tracer termLike $ do
            unfixedTermOr <- descendAndSimplify termLike
            let termOr = OrPattern.coerceSort
                    (termLikeSort termLike)
                    unfixedTermOr
            returnIfSimplifiedOrContinue
                termLike
                (OrPattern.toPatterns termOr)
                (do
                    termPredicateList <- BranchT.gather $ do
                        termOrElement <- BranchT.scatter termOr
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
            return ((`Conditional.andCondition` resultPredicate) <$> simplified)

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
          | isTop resultTerm && Right resultPredicate == termAsPredicate
          = return
                $ OrPattern.fromPattern
                $ Pattern.fromCondition
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
                Condition.fromPredicate <$> Predicate.makePredicate term

    descendAndSimplify :: TermLike variable -> simplifier (OrPattern variable)
    descendAndSimplify termLike =
        let doNotSimplify =
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
            AndF andF ->
                And.simplify sideCondition =<< simplifyChildren andF
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
                        Pattern.mapVariables unTargetElement unTargetSet
                        <$> targetedResults
                return unTargetedResults
              where
                refresh = Lens.over Binding.existsBinder refreshElementBinder
                targetSideCondition
                    :: SideCondition variable
                    -> SideCondition (Target variable)
                targetSideCondition =
                    SideCondition.mapVariables
                        (targetIfEqual boundVar)
                        mkSetNonTarget
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
                (TermLike.ElementVariable boundVar) =
                    TermLike.existsVariable exists
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
            BuiltinF builtinF ->
                Builtin.simplify <$> simplifyChildren builtinF
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
            InternalBytesF internalBytesF ->
                return $ InternalBytes.simplify (getConst internalBytesF)
            VariableF variableF ->
                return $ Variable.simplify (getConst variableF)

    sideConditionRepresentation = SideCondition.toRepresentation sideCondition
