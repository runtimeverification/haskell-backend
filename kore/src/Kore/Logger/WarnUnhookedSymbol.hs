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

warnUnhookedSymbolSeverity :: Severity
warnUnhookedSymbolSeverity = Warning

instance Entry WarnUnhookedSymbol where
    shouldLog minSeverity _ _ = warnUnhookedSymbolSeverity >= minSeverity

    toLogMessage WarnUnhookedSymbol { symbol } =
        LogMessage
            { message =
                "Could not evaluate unhooked symbol:\n" <> unparseToText symbol
            , severity = warnUnhookedSymbolSeverity
            , callstack = emptyCallStack
            }

warnUnhookedSymbol :: MonadLog m => Symbol -> m ()
warnUnhookedSymbol symbol = logM WarnUnhookedSymbol { symbol }
