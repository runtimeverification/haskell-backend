{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.ErrorException
    ( ErrorException
    , errorException
    ) where

import Control.Monad.Catch
    ( SomeException
    , displayException
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )

import Log

newtype ErrorException = ErrorException { getException :: SomeException }

instance Pretty ErrorException where
    pretty = pretty . displayException . getException

instance Entry ErrorException where
    entrySeverity _ = Error

errorException :: MonadLog log => SomeException -> log ()
errorException = logM . ErrorException
