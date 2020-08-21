{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorDecidePredicateUnknown
    ( ErrorDecidePredicateUnknown (..)
    , errorDecidePredicateUnknown
    ) where

import Prelude.Kore

import Control.Exception
    ( Exception (..)
    , throw
    )

import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Variable
import Kore.Unparser
import Log
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

newtype ErrorDecidePredicateUnknown =
    ErrorDecidePredicateUnknown
        { predicates :: NonEmpty (Predicate VariableName)
        }
    deriving (Show)

instance Exception ErrorDecidePredicateUnknown where
    toException = toException . SomeEntry
    fromException exn =
        fromException exn >>= \entry -> fromEntry entry

instance Pretty ErrorDecidePredicateUnknown where
    pretty ErrorDecidePredicateUnknown { predicates } =
        Pretty.vsep
        ( ["Failed to decide predicate:", Pretty.indent 4 (unparse predicate)]
        ++ do
            sideCondition <- sideConditions
            ["with side condition:", Pretty.indent 4 (unparse sideCondition)]
        )
      where
       predicate :| sideConditions = predicates

instance Entry ErrorDecidePredicateUnknown where
    entrySeverity _ = Error
    helpDoc _ =
        "errors raised when the solver cannot decide satisfiability of a formula"

errorDecidePredicateUnknown
    :: InternalVariable variable
    => NonEmpty (Predicate variable)
    -> log ()
errorDecidePredicateUnknown predicates' =
    throw ErrorDecidePredicateUnknown { predicates }
  where
    predicates = Predicate.mapVariables (pure toVariableName) <$> predicates'
