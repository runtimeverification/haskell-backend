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

import           Data.Function
                 ( on )
import           Data.List
                 ( groupBy, sortBy )
import qualified Data.Map as Map
import           Data.Maybe
                 ( mapMaybe )

import Kore.AST.Common
import Kore.AST.Kore
       ( UnifiedPattern, UnifiedSortVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject )
import Kore.AST.PureML
       ( fromPurePattern )
import Kore.AST.Sentence
       ( AsSentence (..), SentenceAxiom (..) )
import Kore.IndexedModule.IndexedModule
       ( IndexedModule (..), KoreIndexedModule )
import Kore.Step.AxiomPatterns
import Kore.Step.Function.Data
       ( ApplicationFunctionEvaluator (..) )
import Kore.Step.Function.UserDefined
       ( axiomFunctionEvaluator )
import Kore.Step.StepperAttributes
       ( StepperAttributes )

{-|Given a 'MetaOrObject' @level@ and a 'KoreIndexedModule',
creates a registry mapping function symbol identifiers to their
corresponding 'AxiomPattern's.
-}
extractFunctionAxioms
    :: MetaOrObject level
    => level
    -> KoreIndexedModule StepperAttributes
    -> Map.Map (Id level) [AxiomPattern level]
extractFunctionAxioms level indexedModule =
    Map.fromList (map extractPrefix groupedAxiomPatterns)
  where
    extractPrefix []                  = error "unexpected case"
    extractPrefix ((a, b) : reminder) = (a, b : map snd reminder)
    groupedAxiomPatterns =
        groupBy
            ((==) `on` fst)
            (sortBy
                (compare `on` fst)
                (mapMaybe
                    (axiomToIdAxiomPatternPair level)
                    (snd <$> indexedModuleAxioms indexedModule))
            )

axiomToIdAxiomPatternPair
    ::  ( MetaOrObject level )
    => level
    -> SentenceAxiom UnifiedSortVariable UnifiedPattern Variable
    -> Maybe (Id level, AxiomPattern level)
axiomToIdAxiomPatternPair
    level
    axiom
  = case koreSentenceToAxiomPattern level (asSentence axiom) of
        Left _ -> Nothing
        Right (FunctionAxiomPattern axiomPat) ->
            case fromPurePattern (axiomPatternLeft axiomPat) of
                ApplicationPattern Application {applicationSymbolOrAlias = s} ->
                    return (symbolOrAliasConstructor s, axiomPat)
                _ -> Nothing
        Right (RewriteAxiomPattern _) -> Nothing

-- |Converts a registry of 'AxiomPattern's to one of
-- 'ApplicationFunctionEvaluator's
axiomPatternsToEvaluators
    :: Map.Map (Id level) [AxiomPattern level]
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
axiomPatternsToEvaluators axiomPatterns =
    -- remove the key if there are no associated function evaluators
    Map.filter (not . null)
        (mapMaybe axiomPatternEvaluator <$> axiomPatterns)

{- | Return the function evaluator corresponding to the 'AxiomPattern'.

@axiomPatternEvaluator@ returns 'Nothing' if the axiom pattern should not be
used as a function evaluator, such as if it is an associativity or commutativity
axiom; this is determined by checking the 'AxiomPatternAttributes'.

 -}
axiomPatternEvaluator
    :: AxiomPattern level
    -> Maybe (ApplicationFunctionEvaluator level)
axiomPatternEvaluator axiomPat@AxiomPattern { axiomPatternAttributes }
    | isAssociativityAxiom = Nothing
    | isCommutativityAxiom = Nothing
    -- TODO (thomas.tuegel): Add unification cases for builtin units and enable
    -- extraction of their axioms.
    | isUnitAxiom = Nothing
    | otherwise =
        Just (ApplicationFunctionEvaluator $ axiomFunctionEvaluator axiomPat)
  where
    AxiomPatternAttributes
        { axiomPatternAssoc = isAssociativityAxiom
        , axiomPatternComm = isCommutativityAxiom
        , axiomPatternUnit = isUnitAxiom
        }
      =
        axiomPatternAttributes
