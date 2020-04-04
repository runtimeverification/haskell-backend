{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.WarnDecidePredicateUnknown
    ( WarnDecidePredicateUnknown (..)
    , warnDecidePredicateUnknown
    ) where

import Prelude.Kore

import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Variable
import Kore.Unparser
import Log
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

data WarnDecidePredicateUnknown =
    WarnDecidePredicateUnknown
        { sideCondition :: !(Maybe (SideCondition Variable))
        , predicate :: !(Predicate Variable)
        }

instance Pretty WarnDecidePredicateUnknown where
    pretty WarnDecidePredicateUnknown { sideCondition, predicate } =
        Pretty.vsep
        [ "Failed to decide predicate:"
        , Pretty.indent 4 (unparse predicate)
        , "under side condition:"
        , Pretty.indent 4 $ unparse $ fromMaybe SideCondition.top sideCondition
        ]

instance Entry WarnDecidePredicateUnknown where
    entrySeverity _ = Warning

warnDecidePredicateUnknown
    :: MonadLog log
    => InternalVariable variable
    => Maybe (SideCondition variable)
    -> Predicate variable
    -> log ()
warnDecidePredicateUnknown sideCondition' predicate' =
    logEntry WarnDecidePredicateUnknown
        { sideCondition
        , predicate
        }
  where
    predicate =
        Predicate.mapVariables
            (fmap toVariable)
            (fmap toVariable)
            predicate'
    sideCondition =
        flip fmap sideCondition'
        $ SideCondition.mapVariables (fmap toVariable) (fmap toVariable)
