{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Log.DebugAppliedRewriteRules (
    DebugAppliedRewriteRules (..),
    debugAppliedRewriteRules,
) where

import Data.Text (Text)
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

data DebugAppliedRewriteRules = DebugAppliedRewriteRules
    { configuration :: !(Pattern VariableName)
    , ruleLabels :: ![Text]
    , appliedRewriteRules :: ![SourceLocation]
    }
    deriving stock (Show)

instance Pretty DebugAppliedRewriteRules where
    pretty DebugAppliedRewriteRules{configuration, appliedRewriteRules} =
        Pretty.vsep $
            (<>)
                prettyUnifiedRules
                [ "On configuration:"
                , Pretty.indent 2 . unparse $ configuration
                ]
      where
        prettyUnifiedRules =
            case appliedRewriteRules of
                [] -> ["No rules were applied."]
                rules ->
                    ["The rules at following locations were applied:"]
                        <> fmap pretty rules

instance Entry DebugAppliedRewriteRules where
    entrySeverity _ = Debug
    helpDoc _ = "log applied rewrite rules"
    oneLineDoc DebugAppliedRewriteRules{appliedRewriteRules} =
        Pretty.hsep $ pretty <$> appliedRewriteRules

debugAppliedRewriteRules ::
    MonadLog log =>
    Pattern RewritingVariableName ->
    [Text] ->
    [SourceLocation] ->
    log ()
debugAppliedRewriteRules initial ruleLabels appliedRewriteRules =
    logEntry
        DebugAppliedRewriteRules
            { configuration
            , ruleLabels
            , appliedRewriteRules
            }
  where
    configuration = mapConditionalVariables TermLike.mapVariables initial
    mapConditionalVariables mapTermVariables =
        Conditional.mapVariables mapTermVariables (pure toVariableName)
