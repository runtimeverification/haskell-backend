{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.WarnMissingHook
    ( WarnMissingHook (..)
    , warnMissingHook
    ) where

import Data.Set
    ( Set
    )
import Data.Text
    ( Text
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Text as Pretty
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
    , MonadLog (logM)
    , Scope
    , Severity (Warning)
    , defaultShouldLog
    )
import Kore.Unparser
    ( unparse
    )

data WarnMissingHook = WarnMissingHook
    { hook :: Text
    , symbol :: Symbol
    } deriving (Eq, Typeable)

missingHookSeverity :: Severity
missingHookSeverity = Warning

instance Entry WarnMissingHook where
    shouldLog :: Severity -> Set Scope -> WarnMissingHook -> Bool
    shouldLog minSeverity currentScope _ =
        defaultShouldLog missingHookSeverity mempty minSeverity currentScope

    toLogMessage :: WarnMissingHook -> LogMessage
    toLogMessage WarnMissingHook { hook, symbol } =
        LogMessage
            { message =
                Pretty.renderStrict
                    . Pretty.layoutPretty Pretty.defaultLayoutOptions
                    $ Pretty.hsep
                        [ "Attempted to evaluate missing hook:"
                        , Pretty.pretty hook
                        , "for symbol:"
                        , unparse symbol
                        ]
            , severity = missingHookSeverity
            , callstack = emptyCallStack
            }

warnMissingHook :: MonadLog m => Text -> Symbol -> m ()
warnMissingHook hook symbol =
    logM $ WarnMissingHook
        { hook
        , symbol
        }
