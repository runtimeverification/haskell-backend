{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Log.DebugSubstitutionSimplifier (
    DebugSubstitutionSimplifier (..),
    whileDebugSubstitutionSimplifier,
    debugSubstitutionSimplifierResult,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified SQL

data DebugSubstitutionSimplifier
    = WhileSimplifySubstitution
    | SubstitutionSimplifierResult
    deriving stock (Show)
    deriving stock (GHC.Generic)

instance SOP.Generic DebugSubstitutionSimplifier

instance SOP.HasDatatypeInfo DebugSubstitutionSimplifier

instance Pretty DebugSubstitutionSimplifier where
    pretty WhileSimplifySubstitution = "Simplifying substitution"
    pretty SubstitutionSimplifierResult = "Non-\\bottom result"

instance Entry DebugSubstitutionSimplifier where
    entrySeverity _ = Debug
    contextDoc _ = Just "while simplifying substitution"
    helpDoc _ = "log non-\\bottom results when normalizing unification solutions"

instance SQL.Table DebugSubstitutionSimplifier

whileDebugSubstitutionSimplifier ::
    MonadLog log =>
    log a ->
    log a
whileDebugSubstitutionSimplifier =
    logWhile WhileSimplifySubstitution

debugSubstitutionSimplifierResult ::
    MonadLog log =>
    log ()
debugSubstitutionSimplifierResult = logEntry SubstitutionSimplifierResult
