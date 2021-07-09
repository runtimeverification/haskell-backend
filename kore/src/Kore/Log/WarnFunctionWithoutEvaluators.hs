{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Log.WarnFunctionWithoutEvaluators (
    WarnFunctionWithoutEvaluators (..),
    warnFunctionWithoutEvaluators,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol (..),
 )
import Kore.Internal.Symbol (
    Symbol (..),
    noEvaluators,
 )
import Kore.Unparser (
    unparse,
 )
import Log (
    Entry (..),
    MonadLog,
    Severity (Warning),
    logEntry,
 )
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty
import qualified SQL

newtype WarnFunctionWithoutEvaluators = WarnFunctionWithoutEvaluators {symbol :: Symbol}
    deriving stock (Show, Eq, Typeable)
    deriving stock (GHC.Generic)

instance SOP.Generic WarnFunctionWithoutEvaluators

instance SOP.HasDatatypeInfo WarnFunctionWithoutEvaluators

instance Pretty WarnFunctionWithoutEvaluators where
    pretty WarnFunctionWithoutEvaluators{symbol} =
        let Symbol{symbolAttributes} = symbol
         in let Attribute.Symbol{klabel, sourceLocation} = symbolAttributes
             in Pretty.vsep
                    [ "No evaluators for function symbol:"
                    , Pretty.indent 4 $
                        Pretty.hsep
                            [ unparse symbol
                            , Pretty.parens $ Pretty.pretty klabel
                            ]
                    , Pretty.hsep
                        [ "defined at:"
                        , Pretty.pretty sourceLocation
                        ]
                    ]

instance Entry WarnFunctionWithoutEvaluators where
    entrySeverity _ = Warning
    helpDoc _ = "warn when encountering a function with no definition"

instance SQL.Table WarnFunctionWithoutEvaluators

warnFunctionWithoutEvaluators :: MonadLog m => Symbol -> m ()
warnFunctionWithoutEvaluators symbol
    | noEvaluators symbol = return ()
    | otherwise = logEntry WarnFunctionWithoutEvaluators{symbol}
