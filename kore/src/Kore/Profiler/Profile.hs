{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

This should be imported @qualified@.
-}
module Kore.Profiler.Profile
    ( axiomBranching
    , axiomEvaluation
    , equalitySimplification
    , executionQueueLength
    , identifierSimplification
    , initialization
    , mergeSubstitutions
    , resimplification
    , simplificationBranching
    , smtDecision
    , timeStrategy
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
    , MonadProfiler (profile, profileConfiguration)
    , profileValue
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
    => Maybe AxiomIdentifier -> thing -> profiler result -> profiler result
equalitySimplification (Just identifier) thing action = do
    Configuration {logEvaluation} <- profileConfiguration
    if logEvaluation
        then do
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
        else action
equalitySimplification Nothing _ action = action

axiomBranching
    :: (MonadProfiler profiler)
    => Maybe AxiomIdentifier -> Int -> Int -> profiler ()
axiomBranching (Just identifier) axiomBranches reevaluationBranches = do
    Configuration {logBranching} <- profileConfiguration
    when (logBranching && (axiomBranches > 1 || reevaluationBranches > 1)) $ do
        profileValue
            [ "branching"
            , "axiom"
            , oneLiner identifier
            ]
            axiomBranches
        profileValue
            [ "branching"
            , "axiom"
            , "reevaluation"
            , oneLiner identifier
            ]
            reevaluationBranches
axiomBranching Nothing _ _ = return ()

simplificationBranching
    :: (MonadProfiler profiler, Unparse thing)
    => String -> thing -> Int -> Int -> profiler ()
simplificationBranching name thing childBranches reevaluationBranches = do
    Configuration {logBranching} <- profileConfiguration
    when (logBranching && (childBranches > 1 || reevaluationBranches > 1)) $ do
        profileValue
            [ "branching"
            , "simplification"
            , "child"
            , name
            , unparseToString thing
            ]
            childBranches
        profileValue
            [ "branching"
            , "simplification"
            , "reevaluation"
            , name
            , unparseToString thing
            ]
            reevaluationBranches

timeStrategy
    :: (MonadProfiler profiler)
    => String -> profiler result -> profiler result
timeStrategy name action = do
    Configuration {logStrategy} <- profileConfiguration
    if logStrategy
        then profile
            [ "strategy"
            , name
            ]
            action
        else action

initialization
    :: (MonadProfiler profiler)
    => String -> profiler result -> profiler result
initialization name action = do
    Configuration {logInitialization} <- profileConfiguration
    if logInitialization
        then profile
            [ "initialization"
            , name
            ]
            action
        else action

identifierSimplification
    :: (MonadProfiler profiler)
    => AxiomIdentifier -> profiler result -> profiler result
identifierSimplification identifier action = do
    Configuration {logSimplification} <- profileConfiguration
    if logSimplification
        then profile
            [ "simplification"
            , oneLiner identifier
            ]
            action
        else action

-- TODO(virgil): Enable this on-demand.
axiomEvaluation
    :: MonadProfiler profiler
    => Maybe AxiomIdentifier -> profiler result -> profiler result
axiomEvaluation (Just identifier) action = do
    Configuration {logEvaluation} <- profileConfiguration
    if logEvaluation
        then filteredLogging
            identifier
            ["evaluate", oneLiner identifier, "1", "apply"]
            action
        else action
axiomEvaluation Nothing action = action

-- TODO(virgil): Enable this on-demand.
resimplification
    :: MonadProfiler profiler
    => Maybe AxiomIdentifier -> Int -> profiler result -> profiler result
resimplification (Just identifier) size action = do
    Configuration {logEvaluation} <- profileConfiguration
    if logEvaluation
        then filteredLogging
            identifier
            ["resimplification", oneLiner identifier, show size]
            action
        else action
resimplification Nothing _ action = action

-- TODO(virgil): Enable this on-demand.
mergeSubstitutions
    :: MonadProfiler profiler
    => Maybe AxiomIdentifier -> profiler result -> profiler result
mergeSubstitutions (Just identifier) action = do
    Configuration {logEvaluation} <- profileConfiguration
    if logEvaluation
        then filteredLogging
            identifier
            ["evaluate", oneLiner identifier, "1", "merge"]
            action
        else action
mergeSubstitutions Nothing action = action

filteredLogging
    :: MonadProfiler profiler
    => AxiomIdentifier
    -> [String]
    -> profiler result
    -> profiler result
filteredLogging identifier tags action = do
    Configuration {identifierFilter} <- profileConfiguration
    case identifierFilter of
        Nothing -> profile tags action
        Just idFilter
          | isSelected idFilter identifier ->
            profile tags action
          | otherwise -> action

isSelected :: String -> AxiomIdentifier -> Bool
isSelected identifierFilter = (== identifierFilter) . oneLiner

smtDecision
    :: MonadProfiler profiler
    => SExpr
    -> profiler result
    -> profiler result
smtDecision sexpr action = do
    Configuration {logSmt} <- profileConfiguration
    if logSmt
        then profile ["SMT", show $ length $ show sexpr] action
        else action

executionQueueLength
    :: MonadProfiler profiler
    => Int -> profiler result -> profiler result
executionQueueLength len action = do
    Configuration {logStrategy} <- profileConfiguration
    when logStrategy
        (profileValue ["ExecutionQueueLength"] len)
    action
