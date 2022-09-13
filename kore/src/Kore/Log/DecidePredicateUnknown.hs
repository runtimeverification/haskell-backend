{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Log.DecidePredicateUnknown (
    OnDecidePredicateUnknown (..),
    DecidePredicateUnknown (..),
    throwDecidePredicateUnknown,
) where

import Control.Exception (
    Exception (..),
    throw,
 )
import Data.Limit (Limit (..))
import Debug
import Kore.Attribute.SourceLocation (
    SourceLocation (..),
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.Variable
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Pretty qualified
import SMT qualified

data OnDecidePredicateUnknown
    = WarnSimplificationEquationInApplication (Maybe SourceLocation)
    | ErrorInApplication (Maybe SourceLocation)
    | ErrorInMatchWith
    | ErrorInSimplifyClaimRule
    | ErrorInFilterMultiOr
    deriving stock (Show, Eq)

data DecidePredicateUnknown = DecidePredicateUnknown
    { action :: OnDecidePredicateUnknown
    , smtLimit :: SMT.RetryLimit
    , predicates :: NonEmpty (Predicate VariableName)
    }
    deriving stock (Show, Eq)

instance Exception DecidePredicateUnknown where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Debug DecidePredicateUnknown where
    debugPrec w = \_ -> Pretty.pretty . show $ w

instance Diff DecidePredicateUnknown where
    diffPrec = diffPrecEq

instance Pretty DecidePredicateUnknown where
    pretty DecidePredicateUnknown{smtLimit = SMT.RetryLimit limit, predicates} =
        Pretty.vsep
            ( [ "Failed to decide predicate:"
              , Pretty.indent 4 (pretty predicate)
              ]
                ++ do
                    sideCondition <- sideConditions
                    [ "with side condition:"
                        , Pretty.indent 4 (pretty sideCondition)
                        ]
                ++ [ "SMT limit set at:"
                   , Pretty.indent
                        4
                        ( case limit of
                            Limit n -> pretty n
                            Unlimited -> "infinity"
                        )
                   ]
            )
      where
        predicate :| sideConditions = predicates

instance Entry DecidePredicateUnknown where
    entrySeverity DecidePredicateUnknown{action} =
        case action of
            WarnSimplificationEquationInApplication _ -> Warning
            _ -> Error
    contextDoc DecidePredicateUnknown{action} =
        Just $
            Pretty.align $
                Pretty.vsep
                    [ Pretty.hsep . catMaybes $
                        [ Just "while applying equation"
                        , (\loc -> Pretty.hsep ["at", pretty loc]) <$> case action of
                            WarnSimplificationEquationInApplication loc -> loc
                            ErrorInApplication loc -> loc
                            _ -> Nothing
                        ]
                    , Pretty.hsep
                        [ "in"
                        , case action of
                            WarnSimplificationEquationInApplication _ ->
                                "Kore.Equation.Application.checkRequires"
                            ErrorInApplication _ ->
                                "Kore.Equation.Application.checkRequires"
                            ErrorInMatchWith ->
                                "Kore.Rewrite.Search.matchWith"
                            ErrorInSimplifyClaimRule ->
                                "Kore.Rewrite.Rule.Simplify.simplifyClaimRule"
                            ErrorInFilterMultiOr ->
                                "Kore.Rewrite.SMT.Evaluator.filterMultiOr"
                        ]
                    ]
    oneLineDoc _ = "DecidePredicateUnknown"
    helpDoc _ =
        "error or a warning when the solver cannot decide the satisfiability of a formula"

throwDecidePredicateUnknown ::
    (MonadLog log, InternalVariable variable) =>
    OnDecidePredicateUnknown ->
    SMT.RetryLimit ->
    NonEmpty (Predicate variable) ->
    log ()
throwDecidePredicateUnknown action smtLimit predicates' =
    case action of
        WarnSimplificationEquationInApplication _ ->
            logEntry DecidePredicateUnknown{action, smtLimit, predicates}
        _ ->
            throw DecidePredicateUnknown{action, smtLimit, predicates}
  where
    predicates = Predicate.mapVariables (pure toVariableName) <$> predicates'
