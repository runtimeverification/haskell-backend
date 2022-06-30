{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Log.DebugAttemptedRewriteRules (
    DebugAttemptedRewriteRules (..),
    debugAttemptedRewriteRule,
) where

import Kore.Attribute.Axiom (
    SourceLocation,
 )
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Internal.Variable (
    VariableName,
    toVariableName,
 )
import Kore.Rewrite.RewritingVariable
import Kore.Unparser
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Pretty qualified

data DebugAttemptedRewriteRules = DebugAttemptedRewriteRules
    { configuration :: ~(Pattern VariableName)
    , attemptedRewriteRule :: SourceLocation
    }
    deriving stock (Show)

instance Pretty DebugAttemptedRewriteRules where
    pretty DebugAttemptedRewriteRules{configuration, attemptedRewriteRule} =
        Pretty.vsep $
            (<>)
                prettyUnifiedRules
                [ "On configuration:"
                , Pretty.indent 2 . unparse $ configuration
                ]
      where
        prettyUnifiedRules =
            ["The rule at following location was attempted:"]
                <> [pretty attemptedRewriteRule]

instance Entry DebugAttemptedRewriteRules where
    entrySeverity _ = Debug
    helpDoc _ = "log attempted rewrite rules"
    oneLineDoc DebugAttemptedRewriteRules{attemptedRewriteRule} =
        pretty attemptedRewriteRule

debugAttemptedRewriteRule ::
    MonadLog log =>
    Pattern RewritingVariableName ->
    SourceLocation ->
    log ()
debugAttemptedRewriteRule initial attemptedRewriteRule =
    logEntry
        DebugAttemptedRewriteRules
            { configuration
            , attemptedRewriteRule
            }
  where
    ~configuration = mapConditionalVariables TermLike.mapVariables initial
    mapConditionalVariables mapTermVariables =
        Conditional.mapVariables mapTermVariables (pure toVariableName)
