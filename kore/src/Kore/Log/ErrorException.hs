{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.ErrorException
    ( ErrorException
    , errorException
    ) where

import Prelude.Kore

import Control.Exception
    ( AssertionFailed
    )
import Control.Monad.Catch
    ( SomeException
    , displayException
    , fromException
    )

import Log
import Pretty
    ( Pretty (..)
    , line
    )

newtype ErrorException =
    ErrorException { getException :: SomeException }
    deriving (Show)

instance Pretty ErrorException where
    pretty err@(ErrorException someException) =
        (pretty . displayException . getException $ err)
        <> pleaseFileBugReport
      where
        pleaseFileBugReport
          | Just _ <- fromException someException :: Maybe AssertionFailed
          = line
            <> "Please file a bug report:\
               \ https://github.com/kframework/kore/issues"
          | otherwise
          = mempty

instance Entry ErrorException where
    entrySeverity _ = Error
    helpDoc _ = "log internal errors"

errorException :: MonadLog log => SomeException -> log ()
errorException = logEntry . ErrorException
