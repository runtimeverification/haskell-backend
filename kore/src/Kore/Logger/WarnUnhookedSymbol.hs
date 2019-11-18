{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Logger.WarnUnhookedSymbol
    ( warnUnhookedSymbol
    ) where

import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )

import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Logger
    ( Entry (..)
    , MonadLog
    , Severity (Warning)
    , logM
    )
import Kore.Unparser
    ( unparse
    )

newtype WarnUnhookedSymbol = WarnUnhookedSymbol
    { symbol :: Symbol
    } deriving (Eq, Typeable)

instance Pretty WarnUnhookedSymbol where
    pretty WarnUnhookedSymbol { symbol } =
        Pretty.vsep
            [ "No evaluators for symbol:"
            , unparse symbol
            ]

instance Entry WarnUnhookedSymbol where
    entrySeverity _ = Warning
    entryScopes _ = mempty

warnUnhookedSymbol :: MonadLog m => Symbol -> m ()
warnUnhookedSymbol symbol = logM WarnUnhookedSymbol { symbol }
