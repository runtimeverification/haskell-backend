{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Logger.CriticalExecutionError
    ( CriticalExecutionError
    , criticalExecutionError
    ) where

import Control.Monad.Catch
    ( SomeException
    , displayException
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )

import Kore.Logger

newtype CriticalExecutionError =
    CriticalExecutionError
    { executionError :: SomeException
    }

instance Pretty CriticalExecutionError where
    pretty CriticalExecutionError { executionError } =
        pretty . displayException $ executionError

instance Entry CriticalExecutionError where
    entrySeverity _ = Critical

criticalExecutionError
    :: MonadLog log
    => SomeException
    -> log ()
criticalExecutionError =
    logM . CriticalExecutionError
