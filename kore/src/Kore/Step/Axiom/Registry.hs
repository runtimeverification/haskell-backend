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
    ) where

import qualified Data.Foldable as Foldable
import Data.List
    ( partition
    )
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Data.Maybe
    ( fromMaybe
    , mapMaybe
    )

import Kore.Attribute.Axiom
    ( Assoc (Assoc)
    , Comm (Comm)
    , Idem (Idem)
    , Unit (Unit)
    )
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Overload
import Kore.Attribute.Simplification
    ( Simplification (..)
    )
import Kore.Attribute.Symbol
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
import Kore.Step.Rule
    ( EqualityRule (EqualityRule)
    , QualifiedAxiomPattern (AllPathClaimPattern, FunctionAxiomPattern, ImplicationAxiomPattern, OnePathClaimPattern, RewriteAxiomPattern)
    , RulePattern (RulePattern)
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
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> Map AxiomIdentifier [EqualityRule Variable]
extractEqualityAxioms =
    Foldable.foldl' extractModuleAxioms Map.empty
    . indexedModulesInScope
  where
    -- | Update the map of function axioms with all the axioms in one module.
    extractModuleAxioms
        :: Map AxiomIdentifier [EqualityRule Variable]
        -> VerifiedModule StepperAttributes Attribute.Axiom
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
        -> (attrs, Verified.SentenceAxiom)
        -> Map AxiomIdentifier [EqualityRule Variable]
    extractSentenceAxiom axioms (_, sentence) =
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
    :: SentenceAxiom (TermLike Variable)
    -> Maybe (AxiomIdentifier, EqualityRule Variable)
axiomToIdAxiomPatternPair axiom =
    case Rule.fromSentenceAxiom axiom of
        Left _ -> Nothing
        Right
            (FunctionAxiomPattern axiomPat@(EqualityRule RulePattern { left }))
          -> do
            identifier <- AxiomIdentifier.matchAxiomIdentifier left
            return (identifier, axiomPat)
        Right (RewriteAxiomPattern _) -> Nothing
        Right (OnePathClaimPattern _) -> Nothing
        Right (AllPathClaimPattern _) -> Nothing
        Right (ImplicationAxiomPattern _) -> Nothing

-- |Converts a registry of 'RulePattern's to one of
-- 'BuiltinAndAxiomSimplifier's
axiomPatternsToEvaluators
    :: Map.Map AxiomIdentifier [EqualityRule Variable]
    -> Map.Map AxiomIdentifier BuiltinAndAxiomSimplifier
axiomPatternsToEvaluators =
    Map.fromAscList . mapMaybe equalitiesToEvaluators . Map.toAscList
  where
    equalitiesToEvaluators
        :: (AxiomIdentifier, [EqualityRule Variable])
        -> Maybe (AxiomIdentifier, BuiltinAndAxiomSimplifier)
    equalitiesToEvaluators
        (symbolId, filter (not . ignoreEqualityRule) -> equalities)
      =
        case (simplificationEvaluator, definitionEvaluator) of
            (Nothing, Nothing) -> Nothing
            (Just evaluator, Nothing) -> Just (symbolId, evaluator)
            (Nothing, Just evaluator) -> Just (symbolId, evaluator)
            (Just sEvaluator, Just dEvaluator) ->
                Just (symbolId, simplifierWithFallback sEvaluator dEvaluator)
      where
        simplifications, evaluations :: [EqualityRule Variable]
        (simplifications, evaluations) =
            partition isSimplificationRule equalities
          where
            isSimplificationRule (EqualityRule RulePattern { attributes }) =
                isSimplification
              where
                Simplification { isSimplification } =
                    Attribute.simplification attributes
        simplification :: [BuiltinAndAxiomSimplifier]
        simplification = simplificationEvaluation <$> simplifications
        simplificationEvaluator =
            if null simplification
                then Nothing
                else Just (firstFullEvaluation simplification)
        definitionEvaluator =
            if null evaluations
                then Nothing
                else Just (definitionEvaluation evaluations)

{- | Return the evaluator corresponding to the 'EqualityRule'.

@ignoreEqualityRule@ returns 'Nothing' if the 'EqualityRule' should not be
used as an evaluator, such as if it is an associativity or commutativity
axiom; this is determined by checking the 'Attribute.Axiom' attributes.

 -}
ignoreEqualityRule :: EqualityRule Variable -> Bool
ignoreEqualityRule (EqualityRule RulePattern { attributes })
    | isAssoc = True
    | isComm = True
    -- TODO (thomas.tuegel): Add unification cases for builtin units and enable
    -- extraction of their axioms.
    | isUnit = True
    | isIdem = True
    | Just _ <- getOverload = True
    | otherwise = False
  where
    Assoc { isAssoc } = Attribute.assoc attributes
    Comm { isComm } = Attribute.comm attributes
    Unit { isUnit } = Attribute.unit attributes
    Idem { isIdem } = Attribute.idem attributes
    Overload { getOverload } = Attribute.overload attributes
