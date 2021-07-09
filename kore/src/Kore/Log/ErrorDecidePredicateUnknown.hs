{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Log.ErrorDecidePredicateUnknown (
    ErrorDecidePredicateUnknown (..),
    errorDecidePredicateUnknown,
) where

import Control.Exception (
    Exception (..),
    throw,
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Variable
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

newtype ErrorDecidePredicateUnknown = ErrorDecidePredicateUnknown
    { predicates :: NonEmpty (Predicate VariableName)
    }
    deriving stock (Show)

instance Exception ErrorDecidePredicateUnknown where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= fromEntry

instance Pretty ErrorDecidePredicateUnknown where
    pretty ErrorDecidePredicateUnknown{predicates} =
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

instance Entry ErrorDecidePredicateUnknown where
    entrySeverity _ = Error
    helpDoc _ =
        "errors raised when the solver cannot decide satisfiability of a formula"

errorDecidePredicateUnknown ::
    InternalVariable variable =>
    NonEmpty (Predicate variable) ->
    log a
errorDecidePredicateUnknown predicates' =
    throw ErrorDecidePredicateUnknown{predicates}
  where
    predicates = Predicate.mapVariables (pure toVariableName) <$> predicates'
