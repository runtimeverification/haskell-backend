{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugAppliedRewriteRules (
    DebugAppliedRewriteRules (..),
    debugAppliedRewriteRules,
) where

import Kore.Attribute.Axiom (
    SourceLocation,
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.TermLike as TermLike
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
import qualified Pretty

data DebugAppliedRewriteRules = DebugAppliedRewriteRules
    { configuration :: Pattern VariableName
    , appliedRewriteRules :: [SourceLocation]
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
        Just $ Pretty.hsep $ pretty <$> appliedRewriteRules

debugAppliedRewriteRules ::
    MonadLog log =>
    Pattern RewritingVariableName ->
    [SourceLocation] ->
    log ()
debugAppliedRewriteRules initial appliedRewriteRules =
    logEntry
        DebugAppliedRewriteRules
            { configuration
            , appliedRewriteRules
            }
  where
    configuration = mapConditionalVariables TermLike.mapVariables initial
    mapConditionalVariables mapTermVariables =
        Conditional.mapVariables mapTermVariables (pure toVariableName)
