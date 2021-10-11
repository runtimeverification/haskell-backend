{- |
Copyright : (c) Runtime Verification, 2020-2021
License   : BSD-3-Clause
-}
module Kore.Log.Debug (
    -- * DebugAppliedRewriteRules
    DebugAppliedRewriteRules (..),
    debugAppliedRewriteRules,

    -- * DebugEvaluateCondition
    DebugEvaluateCondition (..),
    whileDebugEvaluateCondition,
    debugEvaluateConditionResult,

    -- * DebugSubstitutionSimplifier
    DebugSubstitutionSimplifier (..),
    whileDebugSubstitutionSimplifier,
    debugSubstitutionSimplifierResult,

    -- * DebugUnification
    DebugUnification (..),
    WhileDebugUnification (..),
    UnificationSolved (..),
    UnificationUnsolved (..),
    debugUnificationSolved,
    debugUnificationUnsolved,
    whileDebugUnification,

    -- * DebugUnifyBottom
    DebugUnifyBottom (..),
    mkDebugUnifyBottom,
    debugUnifyBottom,
    debugUnifyBottomAndReturnBottom,
) where

import Data.Text (
    Text,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Axiom (
    SourceLocation,
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike (..),
    VariableName,
    toVariableName,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
import Kore.Unparser (
    unparse,
 )
import Log (
    Entry (..),
    MonadLog (..),
    Severity (..),
    logEntry,
 )
import Prelude.Kore
import Pretty (
    Pretty,
    pretty,
    unAnnotate,
 )
import qualified Pretty
import SMT.SimpleSMT (
    Result (..),
 )
import qualified SQL

-- | DebugAppliedRewriteRules
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
        Pretty.hsep $ pretty <$> appliedRewriteRules

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

-- | DebugEvaluateCondition
data DebugEvaluateCondition
    = DebugEvaluateCondition (NonEmpty (Predicate VariableName))
    | DebugEvaluateConditionResult Result
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Pretty DebugEvaluateCondition where
    pretty (DebugEvaluateCondition predicates) =
        Pretty.vsep
            ( [ "evaluating predicate:"
              , Pretty.indent 4 (pretty predicate)
              ]
                ++ do
                    sideCondition <- sideConditions
                    [ "with side condition:"
                        , Pretty.indent 4 (pretty sideCondition)
                        ]
            )
      where
        predicate :| sideConditions = predicates
    pretty (DebugEvaluateConditionResult result) =
        case result of
            Unsat -> "solver returned unsatisfiable"
            Sat -> "solver returned satisfiable"
            Unknown -> "solver returned unknown"

instance Entry DebugEvaluateCondition where
    entrySeverity _ = Debug
    contextDoc _ = Just "while evaluating predicate"
    oneLineDoc (DebugEvaluateCondition _) = "DebugEvaluateCondition _"
    oneLineDoc result = pretty (show result)
    helpDoc _ = "log every predicate evaluated by the SMT solver"

instance SQL.Table DebugEvaluateCondition

whileDebugEvaluateCondition ::
    MonadLog log =>
    InternalVariable variable =>
    NonEmpty (Predicate variable) ->
    log a ->
    log a
whileDebugEvaluateCondition =
    logWhile
        . DebugEvaluateCondition
        . fmap (Predicate.mapVariables (pure toVariableName))

debugEvaluateConditionResult :: MonadLog log => Result -> log ()
debugEvaluateConditionResult = logEntry . DebugEvaluateConditionResult

-- | DebugSubstitutionSimplifier
data DebugSubstitutionSimplifier
    = WhileSimplifySubstitution
    | SubstitutionSimplifierResult
    deriving stock (Show)
    deriving stock (GHC.Generic)

instance SOP.Generic DebugSubstitutionSimplifier

instance SOP.HasDatatypeInfo DebugSubstitutionSimplifier

instance Pretty DebugSubstitutionSimplifier where
    pretty WhileSimplifySubstitution = "Simplifying substitution"
    pretty SubstitutionSimplifierResult = "Non-\\bottom result"

instance Entry DebugSubstitutionSimplifier where
    entrySeverity _ = Debug
    contextDoc _ = Just "while simplifying substitution"
    oneLineDoc = pretty . show
    helpDoc _ = "log non-\\bottom results when normalizing unification solutions"

instance SQL.Table DebugSubstitutionSimplifier

whileDebugSubstitutionSimplifier ::
    MonadLog log =>
    log a ->
    log a
whileDebugSubstitutionSimplifier =
    logWhile WhileSimplifySubstitution

debugSubstitutionSimplifierResult ::
    MonadLog log =>
    log ()
debugSubstitutionSimplifierResult = logEntry SubstitutionSimplifierResult

-- | DebugUnification
data DebugUnification
    = DebugUnificationWhile !WhileDebugUnification
    | DebugUnificationSolved UnificationSolved
    | DebugUnificationUnsolved !UnificationUnsolved
    deriving stock (Show)

instance Pretty DebugUnification where
    pretty (DebugUnificationWhile x) = Pretty.pretty x
    pretty (DebugUnificationSolved x) = Pretty.pretty x
    pretty (DebugUnificationUnsolved x) = Pretty.pretty x

instance Entry DebugUnification where
    entrySeverity _ = Debug
    oneLineDoc (DebugUnificationWhile _) = "DebugUnificationWhile"
    oneLineDoc (DebugUnificationSolved _) = "DebugUnificationSolved"
    oneLineDoc (DebugUnificationUnsolved _) = "DebugUnificationUnsolved"

-- | @WhileDebugUnification@ encloses the context of unification log entries.
data WhileDebugUnification = WhileDebugUnification {term1, term2 :: TermLike VariableName}
    deriving stock (Show)

instance Pretty WhileDebugUnification where
    pretty WhileDebugUnification{term1, term2} =
        Pretty.vsep
            [ "Unifying terms:"
            , Pretty.indent 4 (unparse term1)
            , Pretty.indent 2 "and:"
            , Pretty.indent 4 (unparse term2)
            ]

-- | @UnificationUnsolved@ represents an unsolved unification problem.
data UnificationUnsolved = UnificationUnsolved {term1, term2 :: TermLike VariableName}
    deriving stock (Show)

instance Pretty UnificationUnsolved where
    pretty UnificationUnsolved{term1, term2} =
        Pretty.vsep
            [ "Unification unknown:"
            , Pretty.indent 4 (unparse term1)
            , Pretty.indent 2 "and:"
            , Pretty.indent 4 (unparse term2)
            ]

-- | @UnificationSolved@ represents the solution of a unification problem.
newtype UnificationSolved = UnificationSolved {solution :: Pattern VariableName}
    deriving stock (Show)

instance Pretty UnificationSolved where
    pretty UnificationSolved{solution} =
        Pretty.vsep
            [ "Unification solution:"
            , Pretty.indent 4 (unparse solution)
            ]

whileDebugUnification ::
    MonadLog m =>
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    m a ->
    m a
whileDebugUnification term1' term2' =
    logWhile $ DebugUnificationWhile WhileDebugUnification{term1, term2}
  where
    term1 = TermLike.mapVariables (pure toVariableName) term1'
    term2 = TermLike.mapVariables (pure toVariableName) term2'

debugUnificationSolved ::
    MonadLog m =>
    InternalVariable variable =>
    Pattern variable ->
    m ()
debugUnificationSolved solution' =
    logEntry $ DebugUnificationSolved UnificationSolved{solution}
  where
    solution = Pattern.mapVariables (pure toVariableName) solution'

debugUnificationUnsolved ::
    MonadLog m =>
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    m ()
debugUnificationUnsolved term1' term2' =
    logEntry $ DebugUnificationUnsolved UnificationUnsolved{term1, term2}
  where
    term1 = TermLike.mapVariables (pure toVariableName) term1'
    term2 = TermLike.mapVariables (pure toVariableName) term2'

-- | DebugUnifyBottom
data DebugUnifyBottom = DebugUnifyBottom
    { info :: Text
    , first :: TermLike VariableName
    , second :: TermLike VariableName
    }
    deriving stock (Show, Eq)

instance Pretty DebugUnifyBottom where
    pretty (DebugUnifyBottom info first second) =
        Pretty.vsep
            [ unAnnotate $ pretty info
            , "When unifying:"
            , Pretty.indent 4 . unparse $ first
            , "With:"
            , Pretty.indent 4 . unparse $ second
            ]

instance Entry DebugUnifyBottom where
    entrySeverity _ = Debug
    oneLineDoc _ = "DebugUnifyBottom"
    helpDoc _ = "log failed unification"

mkDebugUnifyBottom ::
    InternalVariable variable =>
    Text ->
    TermLike variable ->
    TermLike variable ->
    DebugUnifyBottom
mkDebugUnifyBottom info first second =
    DebugUnifyBottom
        info
        (TermLike.mapVariables (pure $ from @_ @VariableName) first)
        (TermLike.mapVariables (pure $ from @_ @VariableName) second)

debugUnifyBottom ::
    MonadLog log =>
    InternalVariable variable =>
    Text ->
    TermLike variable ->
    TermLike variable ->
    log ()
debugUnifyBottom info first second =
    logEntry $
        DebugUnifyBottom
            info
            (TermLike.mapVariables (pure $ from @_ @VariableName) first)
            (TermLike.mapVariables (pure $ from @_ @VariableName) second)

debugUnifyBottomAndReturnBottom ::
    MonadUnify log =>
    InternalVariable variable =>
    Text ->
    TermLike variable ->
    TermLike variable ->
    log a
debugUnifyBottomAndReturnBottom info first second = do
    debugUnifyBottom
        info
        first
        second
    empty
