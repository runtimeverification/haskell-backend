{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugEvaluateCondition (
    DebugEvaluateCondition (..),
    whileDebugEvaluateCondition,
    debugEvaluateConditionResult,
) where

import Prelude.Kore

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP

import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Log
import Pretty (
    Pretty (..),
 )
import qualified Pretty
import SMT.SimpleSMT (
    Result (..),
 )
import qualified SQL

data DebugEvaluateCondition
    = DebugEvaluateCondition (NonEmpty (Predicate VariableName))
    | DebugEvaluateConditionResult Result
    deriving (Show)
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Pretty DebugEvaluateCondition where
    pretty (DebugEvaluateCondition predicates) =
        Pretty.vsep
            ( [ "evaluating predicate:"
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
    pretty (DebugEvaluateConditionResult result) =
        case result of
            Unsat -> "solver returned unsatisfiable"
            Sat -> "solver returned satisfiable"
            Unknown -> "solver returned unknown"

instance Entry DebugEvaluateCondition where
    entrySeverity _ = Debug
    shortDoc _ = Just "while evaluating predicate"
    helpDoc _ = "log every predicate evaluated by the SMT solver"

instance SQL.Table DebugEvaluateCondition

whileDebugEvaluateCondition ::
    MonadLog log =>
    InternalVariable variable =>
    NonEmpty (Predicate variable) ->
    log a ->
    log a
whileDebugEvaluateCondition =
    logWhile
        . DebugEvaluateCondition
        . fmap (Predicate.mapVariables (pure toVariableName))

debugEvaluateConditionResult :: MonadLog log => Result -> log ()
debugEvaluateConditionResult = logEntry . DebugEvaluateConditionResult
