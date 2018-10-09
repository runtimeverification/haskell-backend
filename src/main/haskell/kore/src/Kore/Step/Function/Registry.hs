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
    ( extractEvaluators
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
       ( AxiomPattern (..), QualifiedAxiomPattern (..),
       koreSentenceToAxiomPattern )
import Kore.Step.Function.Data
       ( ApplicationFunctionEvaluator (..) )
import Kore.Step.Function.UserDefined
       ( axiomFunctionEvaluator )
import Kore.Step.StepperAttributes
       ( StepperAttributes )

{-|Given a 'MetaOrObject' @level@ and a 'KoreIndexedModule', @extractEvaluators@
creates a registry mapping function symbol identifiers to their
corresponding 'ApplicationFunctionEvaluator's.
-}
extractEvaluators
    :: MetaOrObject level
    => level
    -> KoreIndexedModule StepperAttributes
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
extractEvaluators level indexedModule =
    Map.fromList (map extractPrefix groupedEvaluators)
  where
    extractPrefix []                  = error "unexpected case"
    extractPrefix ((a, b) : reminder) = (a, b : map snd reminder)
    groupedEvaluators =
        groupBy
            ((==) `on` fst)
            (sortBy
                (compare `on` fst)
                (mapMaybe
                    (axiomToIdEvaluatorPair
                        level
                    )
                    (snd <$> indexedModuleAxioms indexedModule))
            )

axiomToIdEvaluatorPair
    ::  ( MetaOrObject level )
    => level
    -> SentenceAxiom UnifiedSortVariable UnifiedPattern Variable
    -> Maybe (Id level, ApplicationFunctionEvaluator level)
axiomToIdEvaluatorPair
    level
    axiom
  = case koreSentenceToAxiomPattern level (asSentence axiom) of
        Left _ -> Nothing
        Right (FunctionAxiomPattern axiomPat) ->
            case fromPurePattern (axiomPatternLeft axiomPat) of
                ApplicationPattern Application {applicationSymbolOrAlias = s} ->
                    return
                        ( symbolOrAliasConstructor s
                        , ApplicationFunctionEvaluator
                            (axiomFunctionEvaluator axiomPat)
                        )
                _ -> Nothing
        Right (RewriteAxiomPattern _) -> Nothing
