{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Equation.Registry
    ( extractEquations
    , partitionEquations
    , PartitionedEquations (..)
    ) where

import Prelude.Kore

import Control.Error
    ( hush
    )
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
import Kore.Equation.Equation
    ( Equation (..)
    )
import qualified Kore.Equation.Equation as Equation
import qualified Kore.Equation.Sentence as Equation
import Kore.IndexedModule.IndexedModule
import Kore.Internal.TermLike
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import Kore.Syntax.Sentence
    ( SentenceAxiom (..)
    )
import qualified Kore.Verified as Verified
import qualified Pretty

{- | Create a mapping from symbol identifiers to their defining axioms.

 -}
extractEquations
    :: VerifiedModule StepperAttributes
    -> Map AxiomIdentifier [Equation VariableName]
extractEquations =
    foldl' moduleWorker Map.empty
    . indexedModulesInScope
  where
    -- | Update the map of function axioms with all the axioms in one module.
    moduleWorker
        :: Map AxiomIdentifier [Equation VariableName]
        -> VerifiedModule StepperAttributes
        -> Map AxiomIdentifier [Equation VariableName]
    moduleWorker axioms imod =
        foldl' sentenceWorker axioms sentences
      where
        sentences = indexedModuleAxioms imod

    -- | Extract an axiom from one sentence and update the map of function
    -- axioms with it. The map is returned unmodified in case the sentence is
    -- not a function axiom.
    sentenceWorker
        :: Map AxiomIdentifier [Equation VariableName]
        -> (Attribute.Axiom Symbol VariableName, Verified.SentenceAxiom)
        -> Map AxiomIdentifier [Equation VariableName]
    sentenceWorker axioms sentence =
        foldl' insertAxiom axioms (identifyEquation sentence)

    -- | Update the map of function axioms by inserting the axiom at the key.
    insertAxiom
        :: Map AxiomIdentifier [Equation VariableName]
        -> (AxiomIdentifier, Equation VariableName)
        -> Map AxiomIdentifier [Equation VariableName]
    insertAxiom axioms (name, patt) =
        Map.alter (Just . (patt :) . fromMaybe []) name axioms

identifyEquation
    ::  ( Attribute.Axiom Symbol VariableName
        , SentenceAxiom (TermLike VariableName)
        )
    ->  Maybe (AxiomIdentifier, Equation VariableName)
identifyEquation axiom = do
    equation@Equation { left } <- hush $ Equation.fromSentenceAxiom axiom
    identifier <- AxiomIdentifier.matchAxiomIdentifier left
    pure (identifier, equation)

data PartitionedEquations =
    PartitionedEquations
        { functionRules       :: ![Equation VariableName]
        , simplificationRules :: ![Equation VariableName]
        }

-- | Filters and partitions a list of 'EqualityRule's to
-- simplification rules and function rules. The function rules
-- are also sorted in order of priority.
partitionEquations
    :: [Equation VariableName]
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

{- | Should we ignore the 'EqualityRule' for evaluation or simplification?

@ignoreEqualityRule@ returns 'True' if the 'EqualityRule' should not be used in
evaluation or simplification, such as if it is an associativity or commutativity
axiom.

 -}
ignoreEquation :: Equation VariableName -> Bool
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
ignoreDefinition :: Equation VariableName -> Bool
ignoreDefinition Equation { attributes, left }
    | isLeftFunctionLike = False
    | otherwise = (error . show . Pretty.vsep)
        [ "left-hand side of equation was not function-like at:"
        , Pretty.indent 4 $ Pretty.pretty sourceLocation
        ]
  where
    Attribute.Axiom { sourceLocation } = attributes
    isLeftFunctionLike =
        (Pattern.isFunction . Pattern.function) (extractAttributes left)
