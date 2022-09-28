{-# OPTIONS_GHC -Wno-orphans #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Log.DebugRewriteTrace (
    DebugInitialClaim (..),
    DebugInitialPattern (..),
    DebugFinalPatterns (..),
    DebugRewriteTrace (..),
    debugInitialClaim,
    debugInitialPattern,
    debugFinalPatterns,
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
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.MultiOr (
    MultiOr,
 )
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
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike qualified as TermLike
import Kore.Internal.TermLike.TermLike (
    TermLike,
 )
import Kore.Internal.Variable (
    VariableName,
    toVariableName,
 )
import Kore.Rewrite.Result qualified as Result
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.RulePattern (
    UnifyingRuleVariable,
 )
import Kore.Rewrite.Step (
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

data DebugInitialClaim = DebugInitialClaim UniqueId (TermLike VariableName)
    deriving stock (Show)

newtype DebugInitialPattern = DebugInitialPattern (TermLike VariableName)
    deriving stock (Show)

newtype DebugFinalPatterns = DebugFinalPatterns [Pattern VariableName]
    deriving stock (Show)

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

instance ToJSON (TermLike VariableName) where
    toJSON = toJSON . unparseOneLine

instance ToJSON (Pattern VariableName) where
    toJSON Conditional.Conditional{term, predicate, substitution} =
        object
            [ "term" .= term
            , "constraint" .= encodedConstraint
            , "substitution" .= substitution
            ]
      where
        sort = TermLike.termLikeSort term
        encodedConstraint = (renderText $ layoutOneLine $ unparseWithSort sort predicate) :: Text

instance ToJSON (Substitution VariableName) where
    toJSON substitution =
        array (encodeKV <$> unwrap substitution)
      where
        encodeKV assignment =
            object
                [ "key" .= unparseOneLine (assignedVariable assignment)
                , "value" .= unparseOneLine (assignedTerm assignment)
                ]

instance ToJSON DebugInitialClaim where
    toJSON (DebugInitialClaim uniqueId claim) =
        object
            [ "task" .= ("reachability" :: Text)
            , "claim" .= claim
            , "claim-id" .= maybe Null toJSON (getUniqueId uniqueId)
            ]

instance ToJSON DebugInitialPattern where
    toJSON (DebugInitialPattern initial) =
        object
            [ "task" .= ("rewriting" :: Text)
            , "initial" .= initial
            ]

instance ToJSON DebugFinalPatterns where
    toJSON (DebugFinalPatterns finals) =
        object
            [ "finals" .= finals
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

instance Pretty DebugInitialClaim where
    pretty = pretty . decodeUtf8 . encode

instance Pretty DebugInitialPattern where
    pretty = pretty . decodeUtf8 . encode

instance Pretty DebugFinalPatterns where
    pretty = pretty . decodeUtf8 . encode

instance Pretty DebugRewriteTrace where
    pretty = pretty . decodeUtf8 . encode

instance Entry DebugInitialClaim where
    entrySeverity _ = Debug
    oneLineDoc (DebugInitialClaim uniqueId _) = "Initial claim " <> maybe mempty pretty (getUniqueId uniqueId)
    helpDoc _ = "log every claim before proving it"

instance Entry DebugInitialPattern where
    entrySeverity _ = Debug
    oneLineDoc (DebugInitialPattern _) = "Initial pattern"
    helpDoc _ = "log initial pattern before rewriting"

instance Entry DebugFinalPatterns where
    entrySeverity _ = Debug
    oneLineDoc (DebugFinalPatterns _) = "Final patterns"
    helpDoc _ = "log final patterns after rewriting"

instance Entry DebugRewriteTrace where
    entrySeverity _ = Debug
    oneLineDoc DebugRewriteTrace{} = "Rewrite trace"
    helpDoc _ = "log rewrite substitutions"

unparseOneLine :: Unparse p => p -> Text
unparseOneLine = renderText . layoutOneLine . unparse

debugInitialClaim ::
    MonadLog log =>
    UniqueId ->
    TermLike VariableName ->
    log ()
debugInitialClaim uniqueId claimPattern = logEntry $ DebugInitialClaim uniqueId claimPattern

debugInitialPattern ::
    MonadLog log =>
    TermLike VariableName ->
    log ()
debugInitialPattern = logEntry . DebugInitialPattern

debugFinalPatterns ::
    MonadLog log =>
    MultiOr (Pattern RewritingVariableName) ->
    log ()
debugFinalPatterns = logEntry . DebugFinalPatterns . (getRewritingPattern <$>) . from

debugRewriteTrace ::
    MonadLog log =>
    UnifyingRuleVariable rule ~ RewritingVariableName =>
    From rule UniqueId =>
    Pattern RewritingVariableName ->
    Results rule ->
    log ()
debugRewriteTrace initial Result.Results{results = (toList -> results), remainders} =
    unless (null results) $
        logEntry
            DebugRewriteTrace
                { initialPattern = getRewritingPattern initial
                , rewriteResults = getResult <$> results
                , remainders = multiOrToList remainders
                }
  where
    mapSubstitutionVariables = Substitution.mapVariables (pure toVariableName)

    multiOrToList = (getRewritingPattern <$>) . from

    getResult Result.Result{appliedRule, result} =
        RewriteResult
            { ruleId = from @_ @UniqueId $ extract appliedRule
            , substitution = mapSubstitutionVariables $ Conditional.substitution appliedRule
            , results = multiOrToList result
            }

rewriteTraceLogger ::
    Applicative m =>
    LogAction m ByteString ->
    LogAction m SomeEntry
rewriteTraceLogger textLogger =
    LogAction action
  where
    action entry
        | Just initial <- fromEntry entry =
            unLogAction textLogger $ "---\n" <> encode (initial :: DebugInitialClaim) <> "steps:"
        | Just initial <- fromEntry entry =
            unLogAction textLogger $ encode (initial :: DebugInitialPattern) <> "steps:"
        | Just final <- fromEntry entry =
            unLogAction textLogger $ encode (final :: DebugFinalPatterns)
        | Just rewrite <- fromEntry entry =
            unLogAction textLogger $ encode [rewrite :: DebugRewriteTrace]
        | otherwise =
            pure ()
