{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.WarnDecidePredicateUnknown
    ( WarnDecidePredicateUnknown (..)
    , warnDecidePredicateUnknown
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

newtype WarnDecidePredicateUnknown =
    WarnDecidePredicateUnknown
        { predicates :: NonEmpty (Predicate Variable)
        }

instance Pretty WarnDecidePredicateUnknown where
    pretty WarnDecidePredicateUnknown { predicates } =
        (Pretty.vsep . concat)
        [ ["Failed to decide predicate:", Pretty.indent 4 (unparse predicate)]
        , do
            sideCondition <- sideConditions
            ["with side condition:", Pretty.indent 4 (unparse sideCondition)]
        ]
      where
       predicate :| sideConditions = predicates

instance Entry WarnDecidePredicateUnknown where
    entrySeverity _ = Warning
    helpDoc _ = "warn when the solver cannot decide satisfiability of a formula"

warnDecidePredicateUnknown
    :: MonadLog log
    => InternalVariable variable
    => NonEmpty (Predicate variable)
    -> log ()
warnDecidePredicateUnknown predicates' =
    logEntry WarnDecidePredicateUnknown { predicates }
  where
    predicates =
        Predicate.mapVariables
            (fmap toVariable)
            (fmap toVariable)
        <$> predicates'
