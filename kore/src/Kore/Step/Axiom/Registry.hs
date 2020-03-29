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
    , mkEvaluatorRegistry
    , partitionEquations
    , PartitionedEquations (..)
    ) where

import Prelude.Kore

import Control.Error
    ( hush
    )
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
import Kore.Equation
    ( Equation (..)
    )
import qualified Kore.Equation as Equation
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
    -> Map AxiomIdentifier [Equation Variable]
extractEqualityAxioms =
    Foldable.foldl' extractModuleAxioms Map.empty
    . indexedModulesInScope
  where
    -- | Update the map of function axioms with all the axioms in one module.
    extractModuleAxioms
        :: Map AxiomIdentifier [Equation Variable]
        -> VerifiedModule StepperAttributes
        -> Map AxiomIdentifier [Equation Variable]
    extractModuleAxioms axioms imod =
        Foldable.foldl' extractSentenceAxiom axioms sentences
      where
        sentences = indexedModuleAxioms imod

    -- | Extract an axiom from one sentence and update the map of function
    -- axioms with it. The map is returned unmodified in case the sentence is
    -- not a function axiom.
    extractSentenceAxiom
        :: Map AxiomIdentifier [Equation Variable]
        -> (Attribute.Axiom Symbol Variable, Verified.SentenceAxiom)
        -> Map AxiomIdentifier [Equation Variable]
    extractSentenceAxiom axioms sentence =
        let
            namedAxiom = axiomToIdAxiomPatternPair sentence
        in
            Foldable.foldl' insertAxiom axioms namedAxiom

    -- | Update the map of function axioms by inserting the axiom at the key.
    insertAxiom
        :: Map AxiomIdentifier [Equation Variable]
        -> (AxiomIdentifier, Equation Variable)
        -> Map AxiomIdentifier [Equation Variable]
    insertAxiom axioms (name, patt) =
        Map.alter (Just . (patt :) . fromMaybe []) name axioms

axiomToIdAxiomPatternPair
    :: (Attribute.Axiom Symbol Variable, SentenceAxiom (TermLike Variable))
    -> Maybe (AxiomIdentifier, Equation Variable)
axiomToIdAxiomPatternPair axiom = do
    equation@Equation { left } <- hush $ Equation.fromSentenceAxiom axiom
    identifier <- AxiomIdentifier.matchAxiomIdentifier left
    pure (identifier, equation)

data PartitionedEquations =
    PartitionedEquations
        { functionRules       :: ![Equation Variable]
        , simplificationRules :: ![Equation Variable]
        }

-- | Filters and partitions a list of 'EqualityRule's to
-- simplification rules and function rules. The function rules
-- are also sorted in order of priority.
partitionEquations
    :: [Equation Variable]
    -> PartitionedEquations
partitionEquations equations =
    PartitionedEquations
        { functionRules
        , simplificationRules
        }
  where
    equations' =
        equations
        & filter (not . ignoreEquation)
    (simplificationRules, unProcessedFunctionRules) =
        partition Equation.isSimplificationRule
        . sortOn Equation.equationPriority
        $ equations'
    functionRules = filter (not . ignoreDefinition) unProcessedFunctionRules

-- | Converts a collection of processed 'EqualityRule's to one of
-- 'BuiltinAndAxiomSimplifier's
equalitiesToEvaluators
    :: PartitionedEquations
    -> Maybe BuiltinAndAxiomSimplifier
equalitiesToEvaluators
    PartitionedEquations { functionRules, simplificationRules }
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
                . from
                <$> simplificationRules
    definitionEvaluator =
        if null functionRules
            then Nothing
            else Just . definitionEvaluation $ from <$> functionRules

mkEvaluatorRegistry
    :: Map AxiomIdentifier [Equation Variable]
    -> Map AxiomIdentifier BuiltinAndAxiomSimplifier
mkEvaluatorRegistry =
    mapMaybe (equalitiesToEvaluators . partitionEquations)

{- | Should we ignore the 'EqualityRule' for evaluation or simplification?

@ignoreEqualityRule@ returns 'True' if the 'EqualityRule' should not be used in
evaluation or simplification, such as if it is an associativity or commutativity
axiom.

 -}
ignoreEquation :: Equation Variable -> Bool
ignoreEquation Equation { attributes }
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
ignoreDefinition :: Equation Variable -> Bool
ignoreDefinition Equation { left } =
    assert isLeftFunctionLike False
  where
    isLeftFunctionLike =
        (Pattern.isFunction . Pattern.function) (extractAttributes left)
