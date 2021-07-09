{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Log.ErrorException (
    ErrorException,
    errorException,
) where

import Control.Exception (
    AssertionFailed,
 )
import Control.Monad.Catch (
    SomeException,
    fromException,
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
    hsep,
    prettyException,
    vsep,
 )

newtype ErrorException = ErrorException {getException :: SomeException}
    deriving stock (Show)

instance Pretty ErrorException where
    pretty (ErrorException someException) =
        (vsep . catMaybes)
            [ Just $ prettyException someException
            , pleaseFileBugReport
            ]
      where
        pleaseFileBugReport = do
            _ <- fromException someException :: Maybe AssertionFailed
            (pure . hsep)
                [ "Please file a bug report:"
                , "https://github.com/kframework/kore/issues"
                ]

instance Entry ErrorException where
    entrySeverity _ = Error
    helpDoc _ = "log internal errors"

errorException :: MonadLog log => SomeException -> log ()
errorException = logEntry . ErrorException
