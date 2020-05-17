{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.ErrorException
    ( ErrorException
    , errorException
    ) where

import Prelude.Kore

import Control.Monad.Catch
    ( SomeException
    , displayException
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )

import Log

newtype ErrorException =
    ErrorException { getException :: SomeException }
    deriving (Show)

instance Pretty ErrorException where
    pretty = pretty . displayException . getException

instance Entry ErrorException where
    entrySeverity _ = Error
    helpDoc _ = "log internal errors"

errorException :: MonadLog log => SomeException -> log ()
errorException = logEntry . ErrorException
