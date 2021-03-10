{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.ErrorVerify (
    ErrorVerify (..),
    errorVerify,
) where

import Prelude.Kore

import Control.Monad.Catch (
    Exception (..),
    MonadThrow,
    throwM,
 )
import Pretty

import Kore.ASTVerifier.Error (
    VerifyError,
 )
import qualified Kore.Error as Kore
import Log

newtype ErrorVerify = ErrorVerify {koreError :: Kore.Error VerifyError}
    deriving (Show)

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
