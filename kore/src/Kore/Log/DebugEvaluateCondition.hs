{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.DebugEvaluateCondition
    ( DebugEvaluateCondition (..)
    , debugEvaluateCondition
    ) where

import Prelude.Kore

import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Unparser
import Log
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import qualified SQL

newtype DebugEvaluateCondition =
    DebugEvaluateCondition { getPredicates :: NonEmpty (Predicate Variable) }
    deriving (GHC.Generic)

instance SOP.Generic DebugEvaluateCondition

instance SOP.HasDatatypeInfo DebugEvaluateCondition

instance Pretty DebugEvaluateCondition where
    pretty (DebugEvaluateCondition (predicate :| sideConditions)) =
        (Pretty.vsep . concat)
        [ [ "evaluating predicate:" , Pretty.indent 4 (unparse predicate) ]
        , do
            sideCondition <- sideConditions
            [ "with side condition:", Pretty.indent 4 (unparse sideCondition) ]
        ]

instance Entry DebugEvaluateCondition where
    entrySeverity _ = Debug

instance SQL.Table DebugEvaluateCondition

debugEvaluateCondition
    :: MonadLog log
    => InternalVariable variable
    => NonEmpty (Predicate variable)
    -> log ()
debugEvaluateCondition =
    logEntry . DebugEvaluateCondition . fmap Predicate.externalizeFreshVariables
