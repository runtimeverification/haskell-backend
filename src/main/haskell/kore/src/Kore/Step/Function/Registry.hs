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
       ( ApplicationFunctionEvaluator (..),
       CommonApplicationFunctionEvaluator )
import Kore.Step.Function.UserDefined
       ( axiomFunctionEvaluator )
import Kore.Step.StepperAttributes
       ( StepperAttributes )

{-|Given a 'MetaOrObject' @level@ and a 'KoreIndexedModule', @extractEvaluators@
creates a registry mapping function symbol identifiers to their
corresponding 'CommonApplicationFunctionEvaluator's.
-}
extractEvaluators
    :: MetaOrObject level
    => level
    -> KoreIndexedModule StepperAttributes
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level domain]
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
                    )
                    (snd <$> indexedModuleAxioms indexedModule))
            )

axiomToIdEvaluatorPair
    :: MetaOrObject level
    => level
    -> SentenceAxiom UnifiedSortVariable UnifiedPattern domain Variable
    -> Maybe (Id level, CommonApplicationFunctionEvaluator level domain)
axiomToIdEvaluatorPair
    level
    axiom
  = case koreSentenceToAxiomPattern level domain (asSentence axiom) of
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
