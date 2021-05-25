{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Log.DebugRewriteSubstitution (
    DebugRewriteSubstitution (..),
    debugRewriteSubstitution,
    rewriteTraceLogger,
) where

import Kore.Attribute.UniqueId (
    UniqueId (..),
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Predicate (
    unparseWithSort,
 )
import Kore.Internal.Substitution (
    Substitution,
    assignedTerm,
    assignedVariable,
    unwrap,
 )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable (
    VariableName,
    toVariableName,
 )
import Kore.Rewriting.RewritingVariable
import Kore.Step.RulePattern (
    UnifyingRuleVariable,
 )
import Kore.Step.Step (
    UnifiedRule,
 )
import Kore.Unparser (
    Unparse,
    unparse,
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
    renderText,
    layoutOneLine,
 )
import Data.Yaml (
    Value (..),
    ToJSON,
    toJSON,
    object,
    (.=),
    encode,
 )
import Data.ByteString (
    ByteString,
 )
import Data.Text (
    Text,
 )
import Data.Text.Encoding (
    decodeUtf8,
 )
import qualified Data.Vector as Vector

data DebugRewriteSubstitution = DebugRewriteSubstitution
    { configuration :: Pattern VariableName
    , appliedRules :: [(UniqueId, Substitution VariableName)]
    }
    deriving stock (Show)

instance ToJSON DebugRewriteSubstitution where
    toJSON DebugRewriteSubstitution{configuration, appliedRules} =
        Array $ Vector.fromList $ encodeRule <$> appliedRules
      where
        unparseOneLine :: Unparse p => p -> Text
        unparseOneLine = renderText . layoutOneLine . unparse

        encodeRule :: (UniqueId, Substitution VariableName) -> Value
        encodeRule (uniqueId, substitution) =
            object [
                "type" .= ("rewriting" :: Text),
                "from" .= unparseOneLine term,
                "constraint" .= encodedConstraint,
                "rule-id" .= encodedUniqueId,
                "substitution" .= encodedSubstitution
            ]
          where
            term = Conditional.term configuration
            sort = TermLike.termLikeSort term
            constraint = Conditional.predicate configuration

            encodedSubstitution = encodeKV <$> unwrap substitution
            encodedConstraint = (renderText $ layoutOneLine $ unparseWithSort sort constraint) :: Text
            encodedUniqueId = maybe Null toJSON (getUniqueId uniqueId)
            encodeKV assignment =
                object [
                    "key" .= unparseOneLine (assignedVariable assignment),
                    "value" .= unparseOneLine (assignedTerm assignment)
                ]

instance Pretty DebugRewriteSubstitution where
    pretty = pretty . decodeUtf8 . encode

instance Entry DebugRewriteSubstitution where
    entrySeverity _ = Debug
    helpDoc _ = "log rewrite substitution"

debugRewriteSubstitution ::
    MonadLog log =>
    UnifyingRuleVariable rule ~ RewritingVariableName =>
    From rule UniqueId =>
    Pattern RewritingVariableName ->
    [UnifiedRule rule] ->
    log ()
debugRewriteSubstitution initial unifiedRules =
    logEntry (DebugRewriteSubstitution configuration appliedRules)
  where
    configuration = Conditional.mapVariables TermLike.mapVariables (pure toVariableName) initial
    appliedRules = uniqueIdAndSubstitution <$> unifiedRules

    mapSubstitutionVariables = Substitution.mapVariables (pure toVariableName)
    uniqueIdAndSubstitution rule =
        (from @_ @UniqueId (extract rule), mapSubstitutionVariables (Conditional.substitution rule))

rewriteTraceLogger ::
    Applicative m =>
    LogAction m ByteString ->
    LogAction m ActualEntry
rewriteTraceLogger textLogger =
    LogAction action
  where
    action ActualEntry{actualEntry}
        | Just rewrite <- fromEntry actualEntry =
            unLogAction textLogger $ encode (rewrite :: DebugRewriteSubstitution)
        | otherwise =
            pure ()
