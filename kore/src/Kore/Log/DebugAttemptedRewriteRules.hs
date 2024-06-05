{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Log.DebugAttemptedRewriteRules (
    DebugAttemptedRewriteRules (..),
    debugAttemptedRewriteRule,
    whileDebugAttemptRewriteRule,
) where

import Data.Aeson (Value (Array), object, toJSON, (.=))
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Vector (fromList)
import Kore.Attribute.Axiom (
    SourceLocation,
    UniqueId (..),
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
import Kore.Util (showHashHex)
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Pretty qualified

data DebugAttemptedRewriteRules = DebugAttemptedRewriteRules
    { configuration :: !(Pattern VariableName)
    , ruleId :: !UniqueId
    , label :: !(Maybe Text)
    , attemptedRewriteRule :: !SourceLocation
    }
    deriving stock (Show)

instance Pretty DebugAttemptedRewriteRules where
    pretty DebugAttemptedRewriteRules{..} =
        Pretty.vsep
            [ (Pretty.hsep . catMaybes)
                [ Just "The rule"
                , (\l -> Pretty.hsep ["with label:", "[", pretty l, "]"]) <$> label
                , Just "at the following location was attempted:"
                , Just . pretty $ attemptedRewriteRule
                ]
            , "On configuration:"
            , Pretty.indent 2 . unparse $ configuration
            ]

shortenRuleId :: Text -> Text
shortenRuleId msg = Text.take 8 msg

shortRuleIdTxt :: UniqueId -> Text
shortRuleIdTxt = shortenRuleId . fromMaybe "UNKNOWN" . getUniqueId

instance Entry DebugAttemptedRewriteRules where
    entrySeverity _ = Debug
    helpDoc _ = "log attempted rewrite rules"

    oneLineContextDoc = \case
        DebugAttemptedRewriteRules{configuration, ruleId} ->
            [ "term " <> (showHashHex $ hash configuration)
            , "rewrite " <> shortRuleIdTxt ruleId
            ]
    oneLineContextJson
        DebugAttemptedRewriteRules{configuration, ruleId} =
            Array $
                fromList
                    [ object
                        [ "term" .= showHashHex (hash configuration)
                        ]
                    , object
                        [ "rewrite" .= shortRuleIdTxt ruleId
                        ]
                    ]

    oneLineDoc entry@(DebugAttemptedRewriteRules{configuration, label, ruleId, attemptedRewriteRule}) =
        let context = map Pretty.brackets (pretty <$> oneLineContextDoc entry <> ["detail"])
            logMsg =
                ( Pretty.hsep . concat $
                    [ ["attempting to apply rewrite rule", Pretty.pretty (shortRuleIdTxt ruleId), Pretty.pretty label]
                    , ["at", Pretty.pretty attemptedRewriteRule]
                    , ["to term", Pretty.pretty . showHashHex $ hash configuration, Pretty.group $ unparse configuration]
                    ]
                )
         in mconcat context <> logMsg

    oneLineJson DebugAttemptedRewriteRules{label, attemptedRewriteRule} =
        toJSON $ renderDefault $ maybe (Pretty.pretty attemptedRewriteRule) Pretty.pretty label

whileDebugAttemptRewriteRule ::
    MonadLog log =>
    Pattern RewritingVariableName ->
    UniqueId ->
    Maybe Text ->
    SourceLocation ->
    log a ->
    log a
whileDebugAttemptRewriteRule initial ruleId label attemptedRewriteRule =
    logWhile (DebugAttemptedRewriteRules{..})
  where
    configuration = mapConditionalVariables TermLike.mapVariables initial
    mapConditionalVariables mapTermVariables =
        Conditional.mapVariables mapTermVariables (pure toVariableName)

debugAttemptedRewriteRule ::
    MonadLog log =>
    Pattern RewritingVariableName ->
    UniqueId ->
    Maybe Text ->
    SourceLocation ->
    log ()
debugAttemptedRewriteRule initial ruleId label attemptedRewriteRule =
    logEntry DebugAttemptedRewriteRules{..}
  where
    configuration = mapConditionalVariables TermLike.mapVariables initial
    mapConditionalVariables mapTermVariables =
        Conditional.mapVariables mapTermVariables (pure toVariableName)
