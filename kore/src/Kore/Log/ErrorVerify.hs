{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Log.ErrorVerify (
    ErrorVerify (..),
    errorVerify,
) where

import Control.Monad.Catch (
    Exception (..),
    MonadThrow,
    throwM,
 )
import Kore.ASTVerifier.Error (
    VerifyError,
 )
import qualified Kore.Error as Kore
import Log
import Prelude.Kore
import Pretty

newtype ErrorVerify = ErrorVerify {koreError :: Kore.Error VerifyError}
    deriving stock (Show)

instance Exception ErrorVerify where
    toException = toException . SomeEntry
    fromException exn = fromException exn >>= fromEntry
    displayException = Kore.printError . koreError

instance Pretty ErrorVerify where
    pretty ErrorVerify{koreError} =
        Pretty.pretty (Kore.printError koreError)

instance Entry ErrorVerify where
    entrySeverity _ = Error

errorVerify :: MonadThrow log => Kore.Error VerifyError -> log a
errorVerify koreError =
    throwM ErrorVerify{koreError}
