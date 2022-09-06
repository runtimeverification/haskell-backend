{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Log.WarnDecidePredicateUnknown (
    WarnDecidePredicateUnknown (..),
    warnDecidePredicateUnknown,
) where

import Debug
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

newtype WarnDecidePredicateUnknown = WarnDecidePredicateUnknown
    { predicates :: NonEmpty (Predicate VariableName)
    }
    deriving stock (Show, Eq)

instance Debug WarnDecidePredicateUnknown where
    debugPrec w = \_ -> Pretty.pretty . show $ w

instance Diff WarnDecidePredicateUnknown where
    diffPrec = diffPrecEq

instance Pretty WarnDecidePredicateUnknown where
    pretty WarnDecidePredicateUnknown{predicates} =
        Pretty.vsep
            ( [ "Failed to decide predicate:"
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

instance Entry WarnDecidePredicateUnknown where
    entrySeverity _ = Warning
    oneLineDoc _ = "WarnDecidePredicateUnknown"
    helpDoc _ =
        "warning when the solver cannot decide satisfiability of a formula"

warnDecidePredicateUnknown ::
    (MonadLog log, InternalVariable variable) =>
    NonEmpty (Predicate variable) ->
    log ()
warnDecidePredicateUnknown predicates' =
    logEntry WarnDecidePredicateUnknown{predicates}
  where
    predicates = Predicate.mapVariables (pure toVariableName) <$> predicates'
