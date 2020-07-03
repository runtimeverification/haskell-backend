{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.ErrorDecidePredicateUnknown
    ( ErrorDecidePredicateUnknown (..)
    , errorDecidePredicateUnknown
    ) where

import Prelude.Kore

import Data.List.NonEmpty
    ( NonEmpty (..)
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
    :: MonadLog log
    => InternalVariable variable
    => NonEmpty (Predicate variable)
    -> log ()
errorDecidePredicateUnknown predicates' =
    logEntry ErrorDecidePredicateUnknown { predicates }
  where
    predicates = Predicate.mapVariables (pure toVariableName) <$> predicates'
