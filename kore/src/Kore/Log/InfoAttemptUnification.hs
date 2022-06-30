{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Log.InfoAttemptUnification (
    InfoAttemptUnification (..),
    infoAttemptUnification,
) where

import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
    VariableName,
    toVariableName,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Unparser (
    unparse,
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty,
 )
import Pretty qualified

data InfoAttemptUnification = InfoAttemptUnification {term1, term2 :: ~(TermLike VariableName)}
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Entry InfoAttemptUnification where
    entrySeverity _ = Info
    contextDoc _ = Just "while attempting unification"
    oneLineDoc _ = "InfoAttemptUnification"
    helpDoc _ = "log unification attempts"

instance Pretty InfoAttemptUnification where
    pretty InfoAttemptUnification{term1, term2} =
        Pretty.vsep
            [ "Attempting to unify"
            , Pretty.indent 4 $ unparse term1
            , Pretty.indent 2 "with"
            , Pretty.indent 4 $ unparse term2
            ]

infoAttemptUnification ::
    MonadLog log =>
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    log a ->
    log a
infoAttemptUnification term1' term2' =
    logWhile InfoAttemptUnification{term1, term2}
  where
    mapVariables = TermLike.mapVariables (pure toVariableName)
    ~term1 = mapVariables term1'
    ~term2 = mapVariables term2'
