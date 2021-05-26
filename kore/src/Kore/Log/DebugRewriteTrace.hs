{-# OPTIONS_GHC -Wno-orphans #-}

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
    array,
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
import qualified Kore.Step.Result as Result
import Kore.Step.RulePattern (
    UnifyingRuleVariable,
 )
import Kore.Step.Step (
    Results,
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

data RewriteResult = RewriteResult
    { ruleId :: UniqueId
    , substitution :: Substitution VariableName
    , results :: [Pattern VariableName]
    }
    deriving stock (Show)

data DebugRewriteTrace = DebugRewriteTrace
    { initialPattern :: Pattern VariableName
    , rewriteResults :: [RewriteResult]
    , remainders :: [Pattern VariableName]
    }
    deriving stock (Show)

instance ToJSON (Pattern VariableName) where
    toJSON patern =
        object
            [ "term" .= unparseOneLine term
            , "constraint" .= encodedConstraint
            ]
      where
        term = Conditional.term patern
        sort = TermLike.termLikeSort term
        constraint = Conditional.predicate patern
        encodedConstraint = (renderText $ layoutOneLine $ unparseWithSort sort constraint) :: Text

instance ToJSON (Substitution VariableName) where
    toJSON substitution =
        array (encodeKV <$> unwrap substitution)
      where
        encodeKV assignment =
            object
                [ "key" .= unparseOneLine (assignedVariable assignment)
                , "value" .= unparseOneLine (assignedTerm assignment)
                ]

instance ToJSON RewriteResult where
    toJSON RewriteResult{ruleId, substitution, results} =
        object
            [ "rule-id" .= maybe Null toJSON (getUniqueId ruleId)
            , "substitution" .= substitution
            , "results" .= results
            ]

instance ToJSON DebugRewriteTrace where
    toJSON DebugRewriteTrace{initialPattern, rewriteResults, remainders} =
        object
            [ "initial" .= initialPattern
            , "applied-rules" .= rewriteResults
            , "remainders" .= remainders
            ]

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
    Results rule ->
    log ()
debugRewriteTrace initial Result.Results{results, remainders} =
    logEntry
        DebugRewriteTrace
            { initialPattern = mapPatternVariables initial
            , rewriteResults = getResult <$> toList results
            , remainders = multiOrToList remainders
            }
  where
    mapPatternVariables = Conditional.mapVariables TermLike.mapVariables (pure toVariableName)
    mapSubstitutionVariables = Substitution.mapVariables (pure toVariableName)

    multiOrToList = (mapPatternVariables <$>) . from

    getResult Result.Result{appliedRule, result} =
        RewriteResult
            { ruleId = from @_ @UniqueId $ extract appliedRule
            , substitution = mapSubstitutionVariables $ Conditional.substitution $ appliedRule
            , results = multiOrToList result
            }

rewriteTraceLogger ::
    Applicative m =>
    LogAction m ByteString ->
    LogAction m ActualEntry
rewriteTraceLogger textLogger =
    LogAction action
  where
    action ActualEntry{actualEntry}
        | Just rewrite <- fromEntry actualEntry =
            unLogAction textLogger $ encode [rewrite :: DebugRewriteTrace]
        | otherwise =
            pure ()
