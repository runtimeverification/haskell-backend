{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Log.DebugRewriteTrace (
    DebugRewriteTrace (..),
    debugRewriteTrace,
    rewriteTraceLogger,
) where

import Data.ByteString (
    ByteString,
 )
import Data.Text (
    Text,
 )
import Data.Text.Encoding (
    decodeUtf8,
 )
import Data.Yaml (
    ToJSON,
    Value (..),
    encode,
    object,
    toJSON,
    (.=),
 )
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
    layoutOneLine,
    renderText,
 )

data AppliedRule = AppliedRule UniqueId (Substitution VariableName)
    deriving stock (Show)

data DebugRewriteTrace = DebugRewriteTrace
    { configuration :: Pattern VariableName
    , appliedRules :: [AppliedRule]
    }
    deriving stock (Show)

instance ToJSON AppliedRule where
    toJSON (AppliedRule uniqueId substitution) =
        object
            [ "rule-id" .= encodedUniqueId
            , "substitution" .= encodedSubstitution
            ]
      where
        encodedSubstitution = encodeKV <$> unwrap substitution
        encodedUniqueId = maybe Null toJSON (getUniqueId uniqueId)
        encodeKV assignment =
            object
                [ "key" .= unparseOneLine (assignedVariable assignment)
                , "value" .= unparseOneLine (assignedTerm assignment)
                ]

instance ToJSON DebugRewriteTrace where
    toJSON DebugRewriteTrace{configuration, appliedRules} =
        object
            [ "from" .= unparseOneLine term
            , "constraint" .= encodedConstraint
            , "applied-rules" .= appliedRules
            ]
      where
        term = Conditional.term configuration
        sort = TermLike.termLikeSort term
        constraint = Conditional.predicate configuration
        encodedConstraint = (renderText $ layoutOneLine $ unparseWithSort sort constraint) :: Text

instance Pretty DebugRewriteTrace where
    pretty = pretty . decodeUtf8 . encode

instance Entry DebugRewriteTrace where
    entrySeverity _ = Debug
    helpDoc _ = "log rewrite substitution"

unparseOneLine :: Unparse p => p -> Text
unparseOneLine = renderText . layoutOneLine . unparse

debugRewriteTrace ::
    MonadLog log =>
    UnifyingRuleVariable rule ~ RewritingVariableName =>
    From rule UniqueId =>
    Pattern RewritingVariableName ->
    [UnifiedRule rule] ->
    log ()
debugRewriteTrace initial unifiedRules =
    logEntry (DebugRewriteTrace configuration appliedRules)
  where
    configuration = Conditional.mapVariables TermLike.mapVariables (pure toVariableName) initial
    appliedRules = uniqueIdAndSubstitution <$> unifiedRules

    mapSubstitutionVariables = Substitution.mapVariables (pure toVariableName)
    uniqueIdAndSubstitution rule =
        AppliedRule
            (from @_ @UniqueId (extract rule))
            (mapSubstitutionVariables (Conditional.substitution rule))

rewriteTraceLogger ::
    Applicative m =>
    LogAction m ByteString ->
    LogAction m ActualEntry
rewriteTraceLogger textLogger =
    LogAction action
  where
    action ActualEntry{actualEntry}
        | Just rewrite <- fromEntry actualEntry =
            unLogAction textLogger $ encode (rewrite :: DebugRewriteTrace)
        | otherwise =
            pure ()
