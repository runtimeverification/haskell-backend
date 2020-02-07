{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.WarnFunctionWithoutEvaluators
    ( WarnFunctionWithoutEvaluators (..)
    , warnFunctionWithoutEvaluators
    ) where

import Prelude.Kore

import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Internal.Symbol
    ( Symbol
    , noEvaluators
    )
import Kore.Unparser
    ( unparse
    )
import Log
    ( Entry (..)
    , MonadLog
    , Severity (Warning)
    , logEntry
    )
import qualified SQL

newtype WarnFunctionWithoutEvaluators =
    WarnFunctionWithoutEvaluators { symbol :: Symbol }
    deriving (Eq, Typeable)
    deriving (GHC.Generic)

instance SOP.Generic WarnFunctionWithoutEvaluators

instance SOP.HasDatatypeInfo WarnFunctionWithoutEvaluators

instance Pretty WarnFunctionWithoutEvaluators where
    pretty WarnFunctionWithoutEvaluators { symbol } =
        Pretty.vsep
            [ "No evaluators for function symbol:"
            , Pretty.indent 4 (unparse symbol)
            ]

instance Entry WarnFunctionWithoutEvaluators where
    entrySeverity _ = Warning

instance SQL.Table WarnFunctionWithoutEvaluators

warnFunctionWithoutEvaluators :: MonadLog m => Symbol -> m ()
warnFunctionWithoutEvaluators symbol
  | noEvaluators symbol = return ()
  | otherwise = logEntry WarnFunctionWithoutEvaluators { symbol }
