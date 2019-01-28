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

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Data.Foldable as Foldable
import           Data.List
                 ( partition )
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe, isJust, mapMaybe )

import           Kore.AST.Kore
import           Kore.AST.Pure
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
                 ( AxiomSimplifier (..),
                 FunctionEvaluators (FunctionEvaluators) )
import           Kore.Step.Function.Data as FunctionEvaluators
                 ( FunctionEvaluators (..) )
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
    -> Map (Id level) [EqualityRule level]
extractFunctionAxioms level =
    \imod ->
        Foldable.foldl'
            extractModuleAxioms
            Map.empty
            (indexedModulesInScope imod)
  where
    -- | Update the map of function axioms with all the axioms in one module.
    extractModuleAxioms
        :: Map (Id level) [EqualityRule level]
        -> VerifiedModule StepperAttributes AxiomPatternAttributes
        -> Map (Id level) [EqualityRule level]
    extractModuleAxioms axioms imod =
        Foldable.foldl' extractSentenceAxiom axioms sentences
      where
        sentences = indexedModuleAxioms imod

    -- | Extract an axiom from one sentence and update the map of function
    -- axioms with it. The map is returned unmodified in case the sentence is
    -- not a function axiom.
    extractSentenceAxiom
        :: Map (Id level) [EqualityRule level]
        -> (attrs, VerifiedKoreSentenceAxiom)
        -> Map (Id level) [EqualityRule level]
    extractSentenceAxiom axioms (_, sentence) =
        let
            namedAxiom = axiomToIdAxiomPatternPair level sentence
        in
            Foldable.foldl' insertAxiom axioms namedAxiom

    -- | Update the map of function axioms by inserting the axiom at the key.
    insertAxiom
        :: Map (Id level) [EqualityRule level]
        -> (Id level, EqualityRule level)
        -> Map (Id level) [EqualityRule level]
    insertAxiom axioms (name, patt) =
        Map.alter (Just . (patt :) . fromMaybe []) name axioms

axiomToIdAxiomPatternPair
    :: MetaOrObject level
    => level
    -> SentenceAxiom UnifiedSortVariable VerifiedKorePattern
    -> Maybe (Id level, EqualityRule level)
axiomToIdAxiomPatternPair level (asKoreAxiomSentence -> axiom) =
    case verifiedKoreSentenceToAxiomPattern level axiom of
        Left _ -> Nothing
        Right
            (FunctionAxiomPattern
                axiomPat@(EqualityRule RulePattern { left }))
          ->
            case (Cofree.tailF . fromPurePattern) left of
                ApplicationPattern Application { applicationSymbolOrAlias } ->
                    case symbolOrAliasParams of
                        [] -> return (symbolOrAliasConstructor, axiomPat)
                        _ ->
                            -- TODO (thomas.tuegel): Handle matching for
                            -- parameterized symbols, then enable extraction of
                            -- their axioms.
                            Nothing
                  where
                    SymbolOrAlias
                        { symbolOrAliasConstructor
                        , symbolOrAliasParams
                        }
                      =
                        applicationSymbolOrAlias
                _ -> Nothing
        Right (RewriteAxiomPattern _) -> Nothing

-- |Converts a registry of 'RulePattern's to one of
-- 'AxiomSimplifier's
axiomPatternsToEvaluators
    :: forall level
    .  Map.Map (Id level) [EqualityRule level]
    -> Map.Map (Id level) (FunctionEvaluators level)
axiomPatternsToEvaluators axiomPatterns =
    Map.map
        (fromMaybe (error "Unexpected Nothing"))
        -- remove the key if there are no associated function evaluators
        (Map.filter isJust
            (Map.map equalitiesToEvaluators axiomPatterns)
        )
  where
    equalitiesToEvaluators
        :: [EqualityRule level] -> Maybe (FunctionEvaluators level)
    equalitiesToEvaluators equalities =
        if null simplification && null evaluations
        then Nothing
        else Just FunctionEvaluators
            { definitionRules = evaluations
            , simplificationEvaluators = simplification
            }
      where
        simplifications :: [EqualityRule level]
        evaluations :: [EqualityRule level]
        (simplifications, evaluations) =
            partition isSimplificationRule equalities
        simplification = mapMaybe axiomPatternEvaluator simplifications
        isSimplificationRule (EqualityRule RulePattern { attributes }) =
            isSimplification
          where
            Simplification { isSimplification } =
                AxiomPatterns.simplification attributes

{- | Return the function evaluator corresponding to the 'AxiomPattern'.

@axiomPatternEvaluator@ returns 'Nothing' if the axiom pattern should not be
used as a function evaluator, such as if it is an associativity or commutativity
axiom; this is determined by checking the 'AxiomPatternAttributes'.

 -}
axiomPatternEvaluator
    :: EqualityRule level
    -> Maybe (AxiomSimplifier level)
axiomPatternEvaluator axiomPat@(EqualityRule RulePattern { attributes })
    | isAssoc = Nothing
    | isComm = Nothing
    -- TODO (thomas.tuegel): Add unification cases for builtin units and enable
    -- extraction of their axioms.
    | isUnit = Nothing
    | isIdem = Nothing
    | otherwise =
        Just (AxiomSimplifier $ ruleFunctionEvaluator axiomPat)
  where
    Assoc { isAssoc } = AxiomPatterns.assoc attributes
    Comm { isComm } = AxiomPatterns.comm attributes
    Unit { isUnit } = AxiomPatterns.unit attributes
    Idem { isIdem } = AxiomPatterns.idem attributes
