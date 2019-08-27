{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

This should be imported @qualified@.
-}
module Kore.Profiler.Profile
    ( equalitySimplification
    , executionQueueLength
    , smtDecision
    ) where

import           Data.Text.Prettyprint.Doc
                 ( Pretty (..) )
import qualified Data.Text.Prettyprint.Doc as Doc
                 ( LayoutOptions (LayoutOptions), PageWidth (Unbounded), group,
                 layoutSmart )
import qualified Data.Text.Prettyprint.Doc.Render.String as Doc
                 ( renderString )

import Kore.Profiler.Data
       ( MonadProfiler (profileDuration) )
import Kore.Step.Axiom.Identifier
       ( AxiomIdentifier )
import SMT

oneLiner :: Pretty a => a -> String
oneLiner =
    Doc.renderString
    . Doc.layoutSmart (Doc.LayoutOptions Doc.Unbounded)
    . Doc.group
    . pretty

equalitySimplification
    :: MonadProfiler profiler
    => AxiomIdentifier -> profiler result -> profiler result
equalitySimplification identifier =
    profileDuration ["equalitySimplification", oneLiner identifier]

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
