{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Equation.Registry (
    extractEquations,
    partitionEquations,
    PartitionedEquations (..),
) where

import Control.Error (
    hush,
 )
import Data.List (
    partition,
    sortOn,
 )
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Kore.Attribute.Axiom (
    Assoc (Assoc),
    Comm (Comm),
    Idem (Idem),
    NonExecutable (NonExecutable),
    Unit (Unit),
 )
import Kore.Attribute.Axiom qualified as Attribute
import Kore.Attribute.Overload
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import Kore.Equation.Equation (
    Equation (..),
 )
import Kore.Equation.Equation qualified as Equation
import Kore.Equation.Sentence qualified as Equation
import Kore.IndexedModule.IndexedModule
import Kore.Internal.TermLike
import Kore.Rewrite.Axiom.Identifier (
    AxiomIdentifier,
 )
import Kore.Rewrite.Axiom.Identifier qualified as AxiomIdentifier
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Syntax.Sentence (
    SentenceAxiom (..),
 )
import Kore.Verified qualified as Verified
import Prelude.Kore

-- | Create a mapping from symbol identifiers to their defining axioms.
extractEquations ::
    VerifiedModule StepperAttributes ->
    Map AxiomIdentifier [Equation VariableName]
extractEquations =
    foldl' moduleWorker Map.empty
        . indexedModulesInScope
  where
    moduleWorker ::
        Map AxiomIdentifier [Equation VariableName] ->
        VerifiedModule StepperAttributes ->
        Map AxiomIdentifier [Equation VariableName]
    moduleWorker axioms imod =
        foldl' sentenceWorker axioms sentences
      where
        sentences = indexedModuleAxioms imod
    sentenceWorker ::
        Map AxiomIdentifier [Equation VariableName] ->
        (Attribute.Axiom Symbol VariableName, Verified.SentenceAxiom) ->
        Map AxiomIdentifier [Equation VariableName]
    sentenceWorker axioms sentence =
        foldl' insertAxiom axioms (identifyEquation sentence)
    insertAxiom ::
        Map AxiomIdentifier [Equation VariableName] ->
        (AxiomIdentifier, Equation VariableName) ->
        Map AxiomIdentifier [Equation VariableName]
    insertAxiom axioms (name, patt) =
        Map.alter (Just . (patt :) . fromMaybe []) name axioms

identifyEquation ::
    ( Attribute.Axiom Symbol VariableName
    , SentenceAxiom (TermLike VariableName)
    ) ->
    Maybe (AxiomIdentifier, Equation VariableName)
identifyEquation axiom = do
    equation@Equation{left} <- hush $ Equation.fromSentenceAxiom axiom
    identifier <- AxiomIdentifier.matchAxiomIdentifier left
    pure (identifier, equation)

data PartitionedEquations = PartitionedEquations
    { functionRules :: ![Equation RewritingVariableName]
    , simplificationRules :: ![Equation RewritingVariableName]
    }

{- | Filters and partitions a list of 'EqualityRule's to
 simplification rules and function rules. The function rules
 are also sorted in order of priority.
-}
partitionEquations ::
    [Equation RewritingVariableName] ->
    PartitionedEquations
partitionEquations equations =
    PartitionedEquations
        { functionRules
        , simplificationRules
        }
  where
    equations' =
        equations
            & filter (not . ignoreEquation)
    (simplificationRules, functionRules) =
        partition Equation.isSimplificationRule
            . sortOn Equation.equationPriority
            $ equations'

{- | Should we ignore the 'Equation' for evaluation or simplification?

@ignoreEquation@ returns 'True' if the 'EqualityRule' should not be used in
evaluation or simplification, such as if it is an associativity or commutativity
axiom, or if it was marked non-executable.
-}
ignoreEquation :: Equation RewritingVariableName -> Bool
ignoreEquation Equation{attributes}
    | isAssoc = True
    | isComm = True
    -- TODO (thomas.tuegel): Add unification cases for builtin units and enable
    -- extraction of their axioms.
    | isUnit = True
    | isIdem = True
    | isNonExecutable = True
    | Just _ <- getOverload = False
    | otherwise = False
  where
    Assoc{isAssoc} = Attribute.assoc attributes
    Comm{isComm} = Attribute.comm attributes
    Unit{isUnit} = Attribute.unit attributes
    Idem{isIdem} = Attribute.idem attributes
    Overload{getOverload} = Attribute.overload attributes
    NonExecutable{isNonExecutable} = Attribute.nonExecutable attributes
