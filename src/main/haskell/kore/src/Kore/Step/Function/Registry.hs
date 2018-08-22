{-|
Module      : Kore.Step.Function.Registry
Description : Creates a registry of function evaluators
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Registry
    ( extractEvaluators
    ) where

import           Control.Monad
                 ( when )
import           Data.List
                 ( groupBy, sortBy )
import qualified Data.Map as Map
import           Data.Maybe
                 ( mapMaybe )
import           Data.Ord
                 ( comparing )

import Kore.AST.Common
import Kore.AST.Kore
       ( UnifiedPattern, UnifiedSortVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject, asUnified )
import Kore.AST.PureML
       ( fromPurePattern )
import Kore.AST.PureToKore
       ( patternKoreToPure )
import Kore.AST.Sentence
       ( SentenceAxiom (..) )
import Kore.IndexedModule.IndexedModule
       ( IndexedModule (..), KoreIndexedModule )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..), SortTools, extractMetadataTools )
import Kore.Predicate.Predicate
       ( wrapPredicate )
import Kore.Step.AxiomPatterns
       ( AxiomPattern (..) )
import Kore.Step.Function.Data
       ( ApplicationFunctionEvaluator (..),
       CommonApplicationFunctionEvaluator )
import Kore.Step.Function.UserDefined
       ( axiomFunctionEvaluator )
import Kore.Step.StepperAttributes
       ( StepperAttributes )

{-|Given a 'MeraOrObject' @level@ and a 'KoreIndexedModule', @extractEvaluators@
creates a registry mappting function symbol identifiers to their
corresponding 'CommonApplicationFunctionEvaluator's.
-}
extractEvaluators
    :: MetaOrObject level
    => level
    -> KoreIndexedModule StepperAttributes
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level]
extractEvaluators level indexedModule =
    Map.fromList (map extractPrefix groupedEvaluators)
  where
    extractPrefix []                  = error "unexpected case"
    extractPrefix ((a, b) : reminder) = (a, b : map snd reminder)
    groupedEvaluators =
        groupBy
            (\ (a, _) (c, _) -> a == c)
            (sortBy
                (comparing fst)
                (mapMaybe
                    (axiomToIdEvaluatorPair
                        level
                        (extractMetadataTools indexedModule)
                    )
                    (snd <$> indexedModuleAxioms indexedModule))
            )

axiomToIdEvaluatorPair
    :: MetaOrObject level
    => level
    -> MetadataTools level StepperAttributes
    -> SentenceAxiom UnifiedSortVariable UnifiedPattern Variable
    -> Maybe (Id level, CommonApplicationFunctionEvaluator level)
axiomToIdEvaluatorPair
    level
    metadataTools
    SentenceAxiom
        { sentenceAxiomParameters = [axiomSort]
        , sentenceAxiomPattern    = korePattern
        }
  = do
    purePattern <- case patternKoreToPure level korePattern of
        Left _  -> Nothing
        Right p -> return p
    (precondition, reminder) <- case fromPurePattern purePattern of
        ImpliesPattern Implies
            { impliesSort = SortVariableSort sort
            , impliesFirst = f
            , impliesSecond = s
            } -> do
                when (asUnified sort /= axiomSort) Nothing
                return (f, s)
        _ -> Nothing
    (postcondition, rule) <- case fromPurePattern reminder of
        AndPattern And {andFirst = f, andSecond = s} -> return (s, f)
        _                                            -> Nothing
    case fromPurePattern postcondition of
        TopPattern _ -> return ()
        _            -> Nothing
    (left, right) <- case fromPurePattern rule of
        EqualsPattern Equals {equalsFirst = f, equalsSecond = s} ->
            return (f, s)
        _ -> Nothing
    leftSymbol <- case fromPurePattern left of
        ApplicationPattern Application {applicationSymbolOrAlias = s} ->
            return s
        _ -> Nothing
    return
        ( symbolOrAliasConstructor leftSymbol
        , ApplicationFunctionEvaluator
            (axiomFunctionEvaluator
                AxiomPattern
                    { axiomPatternLeft  = left
                    , axiomPatternRight = right
                    , axiomPatternRequires = wrapPredicate precondition
                    }
            )
        )
axiomToIdEvaluatorPair _ _ _ = Nothing
