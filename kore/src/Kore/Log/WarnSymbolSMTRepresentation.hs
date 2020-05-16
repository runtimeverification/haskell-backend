{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.WarnSymbolSMTRepresentation
    ( WarnSymbolSMTRepresentation (..)
    , warnSymbolSMTRepresentation
    ) where

import Prelude.Kore

import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import GHC.Generics as GHC

import Kore.Attribute.Symbol
    ( getSmthook
    , getSmtlib
    )
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Internal.TermLike
import Kore.Unparser
    ( unparse
    )
import Log
import qualified SQL

newtype WarnSymbolSMTRepresentation =
    WarnSymbolSMTRepresentation { symbol :: Symbol }
    deriving (Show, Eq, Typeable)
    deriving (GHC.Generic)

instance SOP.Generic WarnSymbolSMTRepresentation

instance SOP.HasDatatypeInfo WarnSymbolSMTRepresentation

instance Pretty WarnSymbolSMTRepresentation where
    pretty WarnSymbolSMTRepresentation { symbol } =
        Pretty.vsep
            [ "Cannot translate symbol despite being given an SMT-LIB expression"
            , Pretty.indent 4 (unparse symbol)
            ]

instance Entry WarnSymbolSMTRepresentation where
    entrySeverity _ = Warning
    helpDoc _ = "warn when a symbol cannot be translated for the SMT solver, despite being given an explicit translation"

instance SQL.Table WarnSymbolSMTRepresentation

warnSymbolSMTRepresentation :: MonadLog m => Symbol -> m ()
warnSymbolSMTRepresentation
    symbol@Symbol { symbolAttributes = Attribute.Symbol { smtlib, smthook } }
  | (isJust . getSmtlib) smtlib || (isJust . getSmthook) smthook
  = logEntry WarnSymbolSMTRepresentation { symbol }
  | otherwise = return ()
