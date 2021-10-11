{- |
Copyright : (c) Runtime Verification, 2021
License   : BSD-3-Clause
-}
module Kore.Log.Warn (
    -- * WarnClaimRHSIsBottom
    WarnClaimRHSIsBottom (..),
    warnClaimRHSIsBottom,

    -- * WarnDepthLimitExceeded
    WarnDepthLimitExceeded (..),
    warnDepthLimitExceeded,

    -- * WarnFunctionWithoutEvaluators
    WarnFunctionWithoutEvaluators (..),
    warnFunctionWithoutEvaluators,

    -- * WarnNotImplemented
    WarnNotImplemented (..),
    warnNotImplemented,

    -- * WarnRetrySolverQuery
    WarnRetrySolverQuery,
    warnRetrySolverQuery,

    -- * WarnSymbolSMTRepresentation
    WarnSymbolSMTRepresentation (..),
    warnSymbolSMTRepresentation,

    -- * WarnUnsimplifiedPredicate
    WarnUnsimplifiedPredicate (..),
    warnUnsimplifiedPredicate,
) where

import Debug
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiOr (
    MultiOr,
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol (
    Symbol (..),
    noEvaluators,
 )
import Kore.Internal.TermLike (
    Application (..),
    TermLike,
 )

-- Causes cyclical module dependency
-- import Kore.Rewrite.RulePattern (
--    ImplicationRule,
-- )

-- Causes cyclical module dependency
-- import Kore.Reachability.SomeClaim (
--     SomeClaim,
-- )

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Numeric.Natural (
    Natural,
 )

-- Causes cyclical module dependency
--import Kore.Attribute.Definition (
--    KFileLocations (..),
-- )

import Kore.Attribute.SourceLocation (
    SourceLocation,
 )
import Kore.Attribute.Symbol (
    getSmthook,
    getSmtlib,
    sourceLocation,
 )
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Internal.Variable (
    InternalVariable,
    VariableName,
    toVariableName,
 )
import Kore.Rewrite.ClaimPattern (
    ClaimPattern,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Unparser (
    unparse,
 )
import Log (
    Entry (..),
    MonadLog,
    Severity (..),
    logEntry,
 )
import Prelude.Kore
import Pretty (
    Pretty,
    pretty,
 )
import qualified Pretty
import qualified SQL

-- | WarnClaimRHSIsBottom
newtype WarnClaimRHSIsBottom = WarnClaimRHSIsBottom {claim :: ClaimPattern}
    deriving stock (Show)

instance Pretty WarnClaimRHSIsBottom where
    pretty WarnClaimRHSIsBottom{claim} =
        Pretty.hsep
            [ "The right-hand side of the claim is bottom:"
            , prettySourceLocation claim
            ]

instance Entry WarnClaimRHSIsBottom where
    entrySeverity _ = Warning
    helpDoc _ = "warn when the right-hand side of a claim is bottom"
    oneLineDoc WarnClaimRHSIsBottom{claim} = prettySourceLocation claim

prettySourceLocation :: ClaimPattern -> Pretty.Doc ann
prettySourceLocation = Pretty.pretty @SourceLocation . from

warnClaimRHSIsBottom ::
    MonadLog log =>
    ClaimPattern ->
    log ()
warnClaimRHSIsBottom = logEntry . WarnClaimRHSIsBottom

-- | WarnDepthLimitExceeded
newtype WarnDepthLimitExceeded = WarnDepthLimitExceeded {limitExceeded :: Natural}
    deriving stock (Show, Eq)

instance Debug WarnDepthLimitExceeded where
    debugPrec w = \_ -> Pretty.pretty . show $ w

instance Diff WarnDepthLimitExceeded where
    diffPrec = diffPrecEq
instance Pretty WarnDepthLimitExceeded where
    pretty (WarnDepthLimitExceeded n) =
        Pretty.hsep
            ["The depth limit", pretty n, "was exceeded."]

instance Entry WarnDepthLimitExceeded where
    entrySeverity _ = Warning
    oneLineDoc (WarnDepthLimitExceeded limitExceeded) =
        Pretty.pretty limitExceeded
    helpDoc _ = "warn when depth limit is exceeded"

warnDepthLimitExceeded :: MonadLog log => Natural -> log ()
warnDepthLimitExceeded = logEntry . WarnDepthLimitExceeded

-- | WarnFunctionWithoutEvaluators
newtype WarnFunctionWithoutEvaluators = WarnFunctionWithoutEvaluators {symbol :: Symbol}
    deriving stock (Show, Eq, Typeable)
    deriving stock (GHC.Generic)

instance SOP.Generic WarnFunctionWithoutEvaluators

instance SOP.HasDatatypeInfo WarnFunctionWithoutEvaluators

instance Pretty WarnFunctionWithoutEvaluators where
    pretty WarnFunctionWithoutEvaluators{symbol} =
        let Symbol{symbolAttributes} = symbol
         in let Attribute.Symbol{klabel, sourceLocation} = symbolAttributes
             in Pretty.vsep
                    [ "No evaluators for function symbol:"
                    , Pretty.indent 4 $
                        Pretty.hsep
                            [ unparse symbol
                            , Pretty.parens $ Pretty.pretty klabel
                            ]
                    , Pretty.hsep
                        [ "defined at:"
                        , Pretty.pretty sourceLocation
                        ]
                    ]

instance Entry WarnFunctionWithoutEvaluators where
    entrySeverity _ = Warning
    oneLineDoc (WarnFunctionWithoutEvaluators Symbol{symbolAttributes}) =
        Pretty.pretty $ sourceLocation symbolAttributes
    helpDoc _ = "warn when encountering a function with no definition"

instance SQL.Table WarnFunctionWithoutEvaluators

warnFunctionWithoutEvaluators :: MonadLog m => Symbol -> m ()
warnFunctionWithoutEvaluators symbol
    | noEvaluators symbol = return ()
    | otherwise = logEntry WarnFunctionWithoutEvaluators{symbol}

-- | WarnNotImplemented
newtype WarnNotImplemented variable = WarnNotImplemented {notImplementedApp :: Application Symbol (TermLike variable)}
    deriving stock (Show)

instance InternalVariable variable => Pretty (WarnNotImplemented variable) where
    pretty (WarnNotImplemented app) =
        Pretty.vsep
            [ "The following application of a builtin function is not implemented:"
            , unparse app
            ]

instance InternalVariable variable => Entry (WarnNotImplemented variable) where
    entrySeverity _ = Warning
    oneLineDoc (WarnNotImplemented (Application Symbol{symbolAttributes} _)) =
        Pretty.pretty $ sourceLocation symbolAttributes
    helpDoc _ = "warn when we try to evaluate a partial builtin function on unimplemented cases"

warnNotImplemented ::
    MonadLog log =>
    InternalVariable variable =>
    Application Symbol (TermLike variable) ->
    log ()
warnNotImplemented = logEntry . WarnNotImplemented

-- | WarnRetrySolverQuery
newtype WarnRetrySolverQuery = WarnRetrySolverQuery
    {predicates :: NonEmpty (Predicate VariableName)}
    deriving stock (Show)

instance Pretty WarnRetrySolverQuery where
    pretty WarnRetrySolverQuery{predicates} =
        Pretty.vsep $
            [ "The SMT solver initially failed to solve the following query:"
            , Pretty.indent 2 "Decide predicate:"
            , Pretty.indent 4 (pretty predicate)
            , Pretty.indent 2 "with side conditions:"
            ]
                <> fmap (Pretty.indent 4 . pretty) sideConditions
                <> [ "The SMT solver was reset and the query\
                     \ was tried one more time."
                   ]
      where
        predicate :| sideConditions = predicates

instance Entry WarnRetrySolverQuery where
    entrySeverity _ = Warning
    oneLineDoc _ = "WarnRetrySolverQuery"
    helpDoc _ =
        "warning raised when the solver failed to decide\
        \ the satisfiability of a formula, indicating that\
        \ the solver was reset and the formula retried"

warnRetrySolverQuery ::
    InternalVariable variable =>
    MonadLog log =>
    NonEmpty (Predicate variable) ->
    log ()
warnRetrySolverQuery predicates' =
    logEntry WarnRetrySolverQuery{predicates}
  where
    predicates =
        Predicate.mapVariables (pure toVariableName) <$> predicates'

-- | WarnSymbolSMTRepresentation
newtype WarnSymbolSMTRepresentation = WarnSymbolSMTRepresentation {symbol :: Symbol}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic, Typeable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Pretty WarnSymbolSMTRepresentation where
    pretty WarnSymbolSMTRepresentation{symbol} =
        Pretty.vsep
            [ "Cannot translate symbol despite being given an SMT-LIB expression"
            , Pretty.indent 4 (unparse symbol)
            ]

instance Entry WarnSymbolSMTRepresentation where
    entrySeverity _ = Warning
    oneLineDoc (WarnSymbolSMTRepresentation Symbol{symbolAttributes}) =
        Pretty.pretty (sourceLocation symbolAttributes)
    helpDoc _ = "warn when a symbol cannot be translated for the SMT solver, despite being given an explicit translation"

instance SQL.Table WarnSymbolSMTRepresentation

warnSymbolSMTRepresentation :: MonadLog m => Symbol -> m ()
warnSymbolSMTRepresentation
    symbol@Symbol{symbolAttributes = Attribute.Symbol{smtlib, smthook}}
        | (isJust . getSmtlib) smtlib || (isJust . getSmthook) smthook =
            logEntry WarnSymbolSMTRepresentation{symbol}
        | otherwise = return ()

-- | WarnUnsimplifiedPredicate
data WarnUnsimplifiedPredicate = WarnUnsimplifiedPredicate
    { limit :: !Int
    , original :: !(Predicate RewritingVariableName)
    , output :: !(MultiOr (MultiAnd (Predicate RewritingVariableName)))
    }
    deriving stock (Show)

instance Pretty WarnUnsimplifiedPredicate where
    pretty WarnUnsimplifiedPredicate{original, output, limit} =
        Pretty.vsep
            [ Pretty.hsep
                [ "Predicate not simplified after"
                , Pretty.pretty limit
                , "rounds."
                ]
            , "Original predicate:"
            , (Pretty.indent 4) (Pretty.pretty original)
            , Pretty.hsep
                [ "Output after"
                , Pretty.pretty limit
                , "rounds:"
                ]
            , (Pretty.indent 4) (Pretty.pretty output)
            ]

instance Entry WarnUnsimplifiedPredicate where
    entrySeverity _ = Warning
    oneLineDoc WarnUnsimplifiedPredicate{limit} = Pretty.pretty limit
    helpDoc _ = "warn when a predicate is not simplified"

warnUnsimplifiedPredicate ::
    MonadLog log =>
    Int ->
    Predicate RewritingVariableName ->
    MultiOr (MultiAnd (Predicate RewritingVariableName)) ->
    log ()
warnUnsimplifiedPredicate limit original output =
    logEntry WarnUnsimplifiedPredicate{limit, original, output}
