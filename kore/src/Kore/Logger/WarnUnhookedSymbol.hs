{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Logger.WarnUnhookedSymbol
    ( warnUnhookedSymbol
    ) where

import Data.Typeable
    ( Typeable
    )
import GHC.Stack
    ( emptyCallStack
    )

import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Logger
    ( Entry (..)
    , LogMessage (..)
    , MonadLog
    , Severity (Warning)
    , logM
    )
import Kore.Unparser
    ( unparseToText
    )

newtype WarnUnhookedSymbol = WarnUnhookedSymbol
    { symbol :: Symbol
    } deriving (Eq, Typeable)

instance Entry WarnUnhookedSymbol where
    toLogMessage WarnUnhookedSymbol { symbol } =
        LogMessage
            { message =
                "Could not evaluate unhooked symbol:\n" <> unparseToText symbol
            , severity = Warning
            , callstack = emptyCallStack
            }

    entrySeverity _ = Warning

    entryScopes _ = mempty

warnUnhookedSymbol :: MonadLog m => Symbol -> m ()
warnUnhookedSymbol symbol = logM WarnUnhookedSymbol { symbol }
