{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Log.ErrorParse (
    ErrorParse (..),
    errorParse,
) where

import Control.Monad.Catch (
    Exception (..),
    MonadThrow,
    throwM,
 )
import Log
import Prelude.Kore
import Pretty

newtype ErrorParse = ErrorParse {message :: String}
    deriving stock (Show)

instance Exception ErrorParse where
    toException = toException . SomeEntry
    fromException exn = fromException exn >>= fromEntry
    displayException = message

instance Pretty ErrorParse where
    pretty ErrorParse{message} =
        Pretty.pretty message

instance Entry ErrorParse where
    entrySeverity _ = Error

errorParse :: MonadThrow log => String -> log a
errorParse message =
    throwM ErrorParse{message}
