{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Log.DebugAttemptUnification (
    DebugAttemptUnificationStart (..),
    DebugAttemptUnificationEnd (..),
    debugAttemptUnificationStart,
    debugAttemptUnificationEnd,
) where

import Kore.Attribute.Axiom (SourceLocation)
import Prelude.Kore
import Log
import Pretty

newtype DebugAttemptUnificationStart =
    DebugAttemptUnificationStart
        { sourceLocationStart :: SourceLocation
        }
        deriving stock (Show)

newtype DebugAttemptUnificationEnd =
    DebugAttemptUnificationEnd
        { sourceLocationEnd :: SourceLocation
        }
        deriving stock (Show)

instance Pretty DebugAttemptUnificationStart where
    pretty DebugAttemptUnificationStart { sourceLocationStart } =
        pretty sourceLocationStart

instance Pretty DebugAttemptUnificationEnd where
    pretty DebugAttemptUnificationEnd { sourceLocationEnd } =
        pretty sourceLocationEnd

instance Entry DebugAttemptUnificationStart where
    entrySeverity _ = Debug
    helpDoc _ = "signals that the backend has started attempting unification with a rewrite rule"
    oneLineDoc = pretty

instance Entry DebugAttemptUnificationEnd where
    entrySeverity _ = Debug
    helpDoc _ = "signals that the backend has finished attempting unification with a rewrite rule"
    oneLineDoc = pretty

debugAttemptUnificationStart ::
    MonadLog log =>
    SourceLocation ->
    log ()
debugAttemptUnificationStart sourceLocationStart =
    logEntry DebugAttemptUnificationStart { sourceLocationStart}

debugAttemptUnificationEnd ::
    MonadLog log =>
    SourceLocation ->
    log ()
debugAttemptUnificationEnd sourceLocationEnd =
    logEntry DebugAttemptUnificationEnd { sourceLocationEnd }







