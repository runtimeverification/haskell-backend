{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.DebugEvaluateCondition
    ( DebugEvaluateCondition (..)
    , whileDebugEvaluateCondition
    , debugEvaluateConditionResult
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
import SMT.SimpleSMT
    ( Result (..)
    )
import qualified SQL

data DebugEvaluateCondition
    = DebugEvaluateCondition (NonEmpty (Predicate Variable))
    | DebugEvaluateConditionResult Result
    deriving (GHC.Generic)

instance SOP.Generic DebugEvaluateCondition

instance SOP.HasDatatypeInfo DebugEvaluateCondition

instance Pretty DebugEvaluateCondition where
    pretty (DebugEvaluateCondition predicates) =
        (Pretty.vsep . concat)
        [ [ "evaluating predicate:" , Pretty.indent 4 (unparse predicate) ]
        , do
            sideCondition <- sideConditions
            [ "with side condition:", Pretty.indent 4 (unparse sideCondition) ]
        ]
      where
       predicate :| sideConditions = predicates

    pretty (DebugEvaluateConditionResult result) =
        case result of
            Unsat -> "solver returned unsatisfiable"
            Sat -> "solver returned satisfiable"
            Unknown -> "solver returned unknown"

instance Entry DebugEvaluateCondition where
    entrySeverity _ = Debug
    shortDoc _ = Just "while evaluating predicate"
    helpDoc _ = "log predicate evaluation"

instance SQL.Table DebugEvaluateCondition

whileDebugEvaluateCondition
    :: MonadLog log
    => InternalVariable variable
    => NonEmpty (Predicate variable)
    -> log a
    -> log a
whileDebugEvaluateCondition =
    logWhile . DebugEvaluateCondition . fmap Predicate.externalizeFreshVariables

debugEvaluateConditionResult :: MonadLog log => Result -> log ()
debugEvaluateConditionResult = logEntry . DebugEvaluateConditionResult
