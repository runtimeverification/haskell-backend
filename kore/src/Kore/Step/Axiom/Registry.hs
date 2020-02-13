{-|
Module      : Kore.Step.Axiom.Registry
Description : Creates a registry of axiom/builtin-based evaluators.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Axiom.Registry
    ( extractEqualityAxioms
    , axiomPatternsToEvaluators
    , processEqualityRules
    , PartitionedEqualityRules (..)
    ) where

import Prelude.Kore

import qualified Data.Foldable as Foldable
import Data.List
    ( partition
    , sortOn
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map

import Kore.Attribute.Axiom
    ( Assoc (Assoc)
    , Comm (Comm)
    , Idem (Idem)
    , Unit (Unit)
    )
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Overload
import qualified Kore.Attribute.Pattern as Pattern
import Kore.Attribute.Symbol
    ( StepperAttributes
    )
import Kore.IndexedModule.IndexedModule
import Kore.Internal.TermLike
import Kore.Step.Axiom.EvaluationStrategy
    ( definitionEvaluation
    , firstFullEvaluation
    , simplificationEvaluation
    , simplifierWithFallback
    )
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import Kore.Step.EqualityPattern
    ( EqualityPattern (..)
    , EqualityRule (EqualityRule)
    , getPriorityOfRule
    , isSimplificationRule
    )
import Kore.Step.Rule
    ( QualifiedAxiomPattern (..)
    )
import qualified Kore.Step.Rule as Rule
import Kore.Step.Simplification.Simplify
    ( BuiltinAndAxiomSimplifier (..)
    )
import Kore.Syntax.Sentence
    ( SentenceAxiom (..)
    )
import qualified Kore.Verified as Verified

{- | Create a mapping from symbol identifiers to their defining axioms.

 -}
extractEqualityAxioms
    :: VerifiedModule StepperAttributes
    -> Map AxiomIdentifier [EqualityRule Variable]
extractEqualityAxioms =
    Foldable.foldl' extractModuleAxioms Map.empty
    . indexedModulesInScope
  where
    -- | Update the map of function axioms with all the axioms in one module.
    extractModuleAxioms
        :: Map AxiomIdentifier [EqualityRule Variable]
        -> VerifiedModule StepperAttributes
        -> Map AxiomIdentifier [EqualityRule Variable]
    extractModuleAxioms axioms imod =
        Foldable.foldl' extractSentenceAxiom axioms sentences
      where
        sentences = indexedModuleAxioms imod

    -- | Extract an axiom from one sentence and update the map of function
    -- axioms with it. The map is returned unmodified in case the sentence is
    -- not a function axiom.
    extractSentenceAxiom
        :: Map AxiomIdentifier [EqualityRule Variable]
        -> (Attribute.Axiom Symbol, Verified.SentenceAxiom)
        -> Map AxiomIdentifier [EqualityRule Variable]
    extractSentenceAxiom axioms sentence =
        let
            namedAxiom = axiomToIdAxiomPatternPair sentence
        in
            Foldable.foldl' insertAxiom axioms namedAxiom

    -- | Update the map of function axioms by inserting the axiom at the key.
    insertAxiom
        :: Map AxiomIdentifier [EqualityRule Variable]
        -> (AxiomIdentifier, EqualityRule Variable)
        -> Map AxiomIdentifier [EqualityRule Variable]
    insertAxiom axioms (name, patt) =
        Map.alter (Just . (patt :) . fromMaybe []) name axioms

axiomToIdAxiomPatternPair
    :: (Attribute.Axiom Symbol, SentenceAxiom (TermLike Variable))
    -> Maybe (AxiomIdentifier, EqualityRule Variable)
axiomToIdAxiomPatternPair axiom =
    case Rule.fromSentenceAxiom axiom of
        Left _ -> Nothing
        Right
            (FunctionAxiomPattern
                axiomPat@(EqualityRule EqualityPattern { left })
            )
          -> do
            identifier <- AxiomIdentifier.matchAxiomIdentifier left
            return (identifier, axiomPat)
        Right (RewriteAxiomPattern _) -> Nothing
        Right (OnePathClaimPattern _) -> Nothing
        Right (AllPathClaimPattern _) -> Nothing
        Right (ImplicationAxiomPattern _) -> Nothing

data PartitionedEqualityRules =
    PartitionedEqualityRules
        { functionRules       :: ![EqualityRule Variable]
        , simplificationRules :: ![EqualityRule Variable]
        }

-- | Filters and partitions a list of 'EqualityRule's to
-- simplification rules and function rules. The function rules
-- are also sorted in order of priority.
processEqualityRules
    :: [EqualityRule Variable]
    -> PartitionedEqualityRules
processEqualityRules (filter (not . ignoreEqualityRule) -> equalities) =
    PartitionedEqualityRules
        { functionRules
        , simplificationRules
        }
  where
    (simplificationRules, unProcessedFunctionRules) =
        partition isSimplificationRule equalities
    functionRules =
        sortOn getPriorityOfRule
        . filter (not . ignoreDefinition)
        $ unProcessedFunctionRules

-- | Converts a collection of processed 'EqualityRule's to one of
-- 'BuiltinAndAxiomSimplifier's
equalitiesToEvaluators
    :: PartitionedEqualityRules
    -> Maybe BuiltinAndAxiomSimplifier
equalitiesToEvaluators
    PartitionedEqualityRules { functionRules, simplificationRules }
  =
    case (simplificationEvaluator, definitionEvaluator) of
        (Nothing, Nothing) -> Nothing
        (Just evaluator, Nothing) -> Just evaluator
        (Nothing, Just evaluator) -> Just evaluator
        (Just sEvaluator, Just dEvaluator) ->
            Just (simplifierWithFallback dEvaluator sEvaluator)
  where
    simplificationEvaluator =
        if null simplificationRules
            then Nothing
            else
                Just . firstFullEvaluation
                $ simplificationEvaluation
                <$> simplificationRules
    definitionEvaluator =
        if null functionRules
            then Nothing
            else Just $ definitionEvaluation functionRules

axiomPatternsToEvaluators
    :: Map.Map AxiomIdentifier [EqualityRule Variable]
    -> Map.Map AxiomIdentifier BuiltinAndAxiomSimplifier
axiomPatternsToEvaluators =
    mapMaybe (equalitiesToEvaluators . processEqualityRules)

{- | Should we ignore the 'EqualityRule' for evaluation or simplification?

@ignoreEqualityRule@ returns 'True' if the 'EqualityRule' should not be used in
evaluation or simplification, such as if it is an associativity or commutativity
axiom.

 -}
ignoreEqualityRule :: EqualityRule Variable -> Bool
ignoreEqualityRule (EqualityRule EqualityPattern { attributes })
  | isAssoc = True
  | isComm = True
  -- TODO (thomas.tuegel): Add unification cases for builtin units and enable
  -- extraction of their axioms.
  | isUnit = True
  | isIdem = True
  | Just _ <- getOverload = False
  | otherwise = False
  where
    Assoc { isAssoc } = Attribute.assoc attributes
    Comm { isComm } = Attribute.comm attributes
    Unit { isUnit } = Attribute.unit attributes
    Idem { isIdem } = Attribute.idem attributes
    Overload { getOverload } = Attribute.overload attributes

{- | Should we ignore the 'EqualityRule' for evaluating function definitions?
 -}
ignoreDefinition :: EqualityRule Variable -> Bool
ignoreDefinition (EqualityRule EqualityPattern { left }) =
    assert isLeftFunctionLike False
  where
    isLeftFunctionLike =
        (Pattern.isFunction . Pattern.function) (extractAttributes left)
