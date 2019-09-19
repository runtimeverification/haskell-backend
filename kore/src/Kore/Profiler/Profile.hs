{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

This should be imported @qualified@.
-}
module Kore.Profiler.Profile
    ( axiomEvaluation
    , equalitySimplification
    , executionQueueLength
    , mergeSubstitutions
    , resimplification
    , smtDecision
    ) where

import Control.Monad
    ( when
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import qualified Data.Text.Prettyprint.Doc as Doc
    ( LayoutOptions (LayoutOptions)
    , PageWidth (Unbounded)
    , group
    , layoutSmart
    )
import qualified Data.Text.Prettyprint.Doc.Render.String as Doc
    ( renderString
    )

import Kore.Profiler.Data
    ( Configuration (Configuration)
    , MonadProfiler (profileConfiguration, profileDuration)
    )
import qualified Kore.Profiler.Data as Profiler.DoNotUse
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import Kore.Unparser
    ( Unparse
    , unparseToString
    )
import SMT

import Debug.Trace

oneLiner :: Pretty a => a -> String
oneLiner =
    Doc.renderString
    . Doc.layoutSmart (Doc.LayoutOptions Doc.Unbounded)
    . Doc.group
    . pretty

equalitySimplification
    :: (MonadProfiler profiler, Unparse thing)
    => AxiomIdentifier -> thing -> profiler result -> profiler result
equalitySimplification identifier thing action = do
    Configuration {dumpIdentifier} <- profileConfiguration
    let strIdentifier = oneLiner identifier
    -- TODO(virgil): Move this in the logger.
    case dumpIdentifier of
        Just toDump ->
            when (toDump == strIdentifier)
                (traceM (unparseToString thing))
        Nothing -> return ()
    filteredLogging
        identifier ["evaluate", strIdentifier, "0", "total"] action

-- TODO(virgil): Enable this on-demand.
axiomEvaluation
    :: MonadProfiler profiler
    => AxiomIdentifier -> profiler result -> profiler result
axiomEvaluation identifier =
    filteredLogging identifier ["evaluate", oneLiner identifier, "1", "apply"]

-- TODO(virgil): Enable this on-demand.
resimplification
    :: MonadProfiler profiler
    => AxiomIdentifier -> Int -> profiler result -> profiler result
resimplification identifier size =
    filteredLogging
        identifier
        ["resimplification", oneLiner identifier, show size]

-- TODO(virgil): Enable this on-demand.
mergeSubstitutions
    :: MonadProfiler profiler
    => AxiomIdentifier -> profiler result -> profiler result
mergeSubstitutions identifier =
    filteredLogging identifier ["evaluate", oneLiner identifier, "1", "merge"]

filteredLogging
    :: MonadProfiler profiler
    => AxiomIdentifier
    -> [String]
    -> profiler result
    -> profiler result
filteredLogging identifier tags action = do
    Configuration {identifierFilter} <- profileConfiguration
    case identifierFilter of
        Nothing -> profileDuration tags action
        Just idFilter
          | isSelected idFilter identifier ->
            profileDuration tags action
          | otherwise -> action

isSelected :: String -> AxiomIdentifier -> Bool
isSelected identifierFilter = (== identifierFilter) . oneLiner

smtDecision
    :: MonadProfiler profiler
    => SExpr
    -> profiler result
    -> profiler result
smtDecision sexpr =
    profileDuration ["SMT", show $ length $ show sexpr]

executionQueueLength
    :: MonadProfiler profiler
    => Int -> profiler result -> profiler result
executionQueueLength len =
    profileDuration ["ExecutionQueueLength", show len]
