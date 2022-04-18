{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Log.WarnSMTTranslation (
    WarnSMTTranslation (..),
    warnSMTTranslation,
) where

import Control.Monad.Catch (
    Exception (..),
 )
import Data.Maybe (
    fromJust,
 )
import Data.Monoid (
    Last (..),
 )
import Debug
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Log hiding (message)
import Prelude.Kore
import Pretty

newtype WarnSMTTranslation = WarnSMTTranslation {message :: Last String}
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving newtype (Semigroup, Monoid)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Diff, Debug)

instance Exception WarnSMTTranslation where
    toException = toException . SomeEntry
    fromException exn = fromException exn >>= fromEntry
    displayException = fromJust . getLast . message

instance Pretty WarnSMTTranslation where
    pretty WarnSMTTranslation{message} =
        Pretty.pretty $ fromJust $ getLast message

instance Entry WarnSMTTranslation where
    entrySeverity _ = Error
    oneLineDoc _ = "WarnSMTTranslation"

warnSMTTranslation :: String -> Either WarnSMTTranslation a
warnSMTTranslation message = Left WarnSMTTranslation{message = Last $ Just message}
