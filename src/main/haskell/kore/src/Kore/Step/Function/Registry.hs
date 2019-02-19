{-|
Module      : Kore.Step.Function.Registry
Description : Creates a registry of function evaluators
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Registry
    ( extractFunctionAxioms
    , axiomPatternsToEvaluators
    ) where

import qualified Data.Foldable as Foldable
import           Data.List
                 ( partition )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe, isJust, mapMaybe )

import           Kore.AST.Kore
import           Kore.AST.Sentence
import           Kore.Attribute.Simplification
                 ( Simplification (..) )
import           Kore.IndexedModule.IndexedModule
import           Kore.Step.AxiomPatterns
                 ( Assoc (Assoc), AxiomPatternAttributes, Comm (Comm),
                 EqualityRule (EqualityRule), Idem (Idem),
                 QualifiedAxiomPattern (FunctionAxiomPattern, RewriteAxiomPattern),
                 RulePattern (RulePattern), Unit (Unit),
                 verifiedKoreSentenceToAxiomPattern )
import qualified Kore.Step.AxiomPatterns as AxiomPatterns
                 ( Assoc (..), AxiomPatternAttributes (..), Comm (..),
                 Idem (..), RulePattern (..), Unit (..) )
import           Kore.Step.Function.Data
                 ( BuiltinAndAxiomSimplifier (..) )
import           Kore.Step.Function.EvaluationStrategy
                 ( definitionEvaluation, firstFullEvaluation,
                 simplifierWithFallback )
import           Kore.Step.Function.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Function.Identifier as AxiomIdentifier
                 ( extract )
import           Kore.Step.Function.UserDefined
                 ( ruleFunctionEvaluator )
import           Kore.Step.StepperAttributes

{- | Create a mapping from symbol identifiers to their defining axioms.

 -}
extractFunctionAxioms
    ::  forall level.
        MetaOrObject level
    => level
    -> VerifiedModule StepperAttributes AxiomPatternAttributes
    -> Map (AxiomIdentifier level) [EqualityRule level Variable]
extractFunctionAxioms level =
    \imod ->
        Foldable.foldl'
            extractModuleAxioms
            Map.empty
            (indexedModulesInScope imod)
  where
    -- | Update the map of function axioms with all the axioms in one module.
    extractModuleAxioms
        :: Map (AxiomIdentifier level) [EqualityRule level Variable]
        -> VerifiedModule StepperAttributes AxiomPatternAttributes
        -> Map (AxiomIdentifier level) [EqualityRule level Variable]
    extractModuleAxioms axioms imod =
        Foldable.foldl' extractSentenceAxiom axioms sentences
      where
        sentences = indexedModuleAxioms imod

    -- | Extract an axiom from one sentence and update the map of function
    -- axioms with it. The map is returned unmodified in case the sentence is
    -- not a function axiom.
    extractSentenceAxiom
        :: Map (AxiomIdentifier level) [EqualityRule level Variable]
        -> (attrs, VerifiedKoreSentenceAxiom)
        -> Map (AxiomIdentifier level) [EqualityRule level Variable]
    extractSentenceAxiom axioms (_, sentence) =
        let
            namedAxiom = axiomToIdAxiomPatternPair level sentence
        in
            Foldable.foldl' insertAxiom axioms namedAxiom

    -- | Update the map of function axioms by inserting the axiom at the key.
    insertAxiom
        :: Map (AxiomIdentifier level) [EqualityRule level Variable]
        -> (AxiomIdentifier level, EqualityRule level Variable)
        -> Map (AxiomIdentifier level) [EqualityRule level Variable]
    insertAxiom axioms (name, patt) =
        Map.alter (Just . (patt :) . fromMaybe []) name axioms

axiomToIdAxiomPatternPair
    :: MetaOrObject level
    => level
    -> SentenceAxiom UnifiedSortVariable VerifiedKorePattern
    -> Maybe (AxiomIdentifier level, EqualityRule level Variable)
axiomToIdAxiomPatternPair level (asKoreAxiomSentence -> axiom) =
    case verifiedKoreSentenceToAxiomPattern level axiom of
        Left _ -> Nothing
        Right
            (FunctionAxiomPattern axiomPat@(EqualityRule RulePattern { left }))
          -> do
            identifier <- AxiomIdentifier.extract left
            return (identifier, axiomPat)
        Right (RewriteAxiomPattern _) -> Nothing

-- |Converts a registry of 'RulePattern's to one of
-- 'BuiltinAndAxiomSimplifier's
axiomPatternsToEvaluators
    :: forall level
    .  Map.Map (AxiomIdentifier level) [EqualityRule level Variable]
    -> Map.Map (AxiomIdentifier level) (BuiltinAndAxiomSimplifier level)
axiomPatternsToEvaluators axiomPatterns =
    Map.map
        (fromMaybe (error "Unexpected Nothing"))
        -- remove the key if there are no associated function evaluators
        (Map.filter isJust
            (Map.map equalitiesToEvaluators axiomPatterns)
        )
  where
    equalitiesToEvaluators
        :: [EqualityRule level Variable]
        -> Maybe (BuiltinAndAxiomSimplifier level)
    equalitiesToEvaluators equalities =
        case (simplificationEvaluator, definitionEvaluator) of
            (Nothing, Nothing) -> Nothing
            (Just evaluator, Nothing) -> Just evaluator
            (Nothing, Just evaluator) -> Just evaluator
            (Just sEvaluator, Just dEvaluator) ->
                Just (simplifierWithFallback sEvaluator dEvaluator)
      where
        simplifications :: [EqualityRule level Variable]
        nonSimplifications :: [EqualityRule level Variable]
        (simplifications, nonSimplifications) =
            partition isSimplificationRule equalities
        evaluations :: [EqualityRule level Variable]
        evaluations =
            filter
                (\rule ->
                    not (isCommRule rule)
                    && not (isAssocRule rule)
                    && not (isIdemRule rule)
                    && not (isUnitRule rule)
                )
                nonSimplifications
        simplification = mapMaybe axiomPatternEvaluator simplifications
        simplificationEvaluator =
            if null simplification
                then Nothing
                else Just (firstFullEvaluation simplification)
        definitionEvaluator =
            if null evaluations
                then Nothing
                else Just (definitionEvaluation evaluations)
        isSimplificationRule (EqualityRule RulePattern { attributes }) =
            isSimplification
          where
            Simplification { isSimplification } =
                AxiomPatterns.simplification attributes
        isCommRule (EqualityRule RulePattern { attributes }) =
            isComm
          where
            Comm { isComm } = AxiomPatterns.comm attributes
        isAssocRule (EqualityRule RulePattern { attributes }) =
            isAssoc
          where
            Assoc { isAssoc } = AxiomPatterns.assoc attributes
        isIdemRule (EqualityRule RulePattern { attributes }) =
            isIdem
          where
            Idem { isIdem } = AxiomPatterns.idem attributes
        isUnitRule (EqualityRule RulePattern { attributes }) =
            isUnit
          where
            Unit { isUnit } = AxiomPatterns.unit attributes

{- | Return the function evaluator corresponding to the 'AxiomPattern'.

@axiomPatternEvaluator@ returns 'Nothing' if the axiom pattern should not be
used as a function evaluator, such as if it is an associativity or commutativity
axiom; this is determined by checking the 'AxiomPatternAttributes'.

 -}
axiomPatternEvaluator
    :: EqualityRule level Variable
    -> Maybe (BuiltinAndAxiomSimplifier level)
axiomPatternEvaluator axiomPat@(EqualityRule RulePattern { attributes })
    | isAssoc = Nothing
    | isComm = Nothing
    -- TODO (thomas.tuegel): Add unification cases for builtin units and enable
    -- extraction of their axioms.
    | isUnit = Nothing
    | isIdem = Nothing
    | otherwise =
        Just (BuiltinAndAxiomSimplifier $ ruleFunctionEvaluator axiomPat)
  where
    Assoc { isAssoc } = AxiomPatterns.assoc attributes
    Comm { isComm } = AxiomPatterns.comm attributes
    Unit { isUnit } = AxiomPatterns.unit attributes
    Idem { isIdem } = AxiomPatterns.idem attributes
