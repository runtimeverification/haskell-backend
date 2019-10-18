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
import Data.Text.Prettyprint.Doc
    ( (<+>)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )

import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Logger
import Kore.Unparser
    ( unparse
    )


data WarnMissingHook = WarnMissingHook
    { hook :: Text
    , symbol :: Symbol
    } deriving (Eq, Typeable)

instance Pretty.Pretty WarnMissingHook where
    pretty WarnMissingHook { hook, symbol } =
        Pretty.vsep
            [ "Attempted to evaluate missing hook:" <+> Pretty.pretty hook
            , "for symbol:" <+> unparse symbol
            ]

instance Entry WarnMissingHook where
    shouldLog :: Severity -> Set Scope -> WarnMissingHook -> Bool
    shouldLog minSeverity currentScope _ =
        defaultShouldLog severity scope minSeverity currentScope
      where
        severity = Warning
        scope    = [Scope "MissingHooks"]

warnMissingHook :: MonadLog m => Text -> Symbol -> m ()
warnMissingHook hook symbol =
    logM $ WarnMissingHook
        { hook
        , symbol
        }
