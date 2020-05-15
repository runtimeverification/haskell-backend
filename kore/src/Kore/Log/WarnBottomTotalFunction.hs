{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.WarnBottomTotalFunction
    ( WarnBottomTotalFunction (..)
    , warnBottomTotalFunction
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import GHC.Generics as GHC

import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    )
import Kore.Unparser
    ( unparse
    )
import Pretty
    ( Pretty
    )
import qualified Pretty

import Log
import qualified SQL

newtype WarnBottomTotalFunction =
    WarnBottomTotalFunction
        { term :: TermLike Variable
        }
    deriving (GHC.Generic)

instance SOP.Generic WarnBottomTotalFunction

instance SOP.HasDatatypeInfo WarnBottomTotalFunction

instance Pretty WarnBottomTotalFunction where
    pretty WarnBottomTotalFunction { term } =
        Pretty.vsep
            [ "Evaluating total function"
            , Pretty.indent 4 (unparse term)
            , "has resulted in \\bottom."
            ]

instance Entry WarnBottomTotalFunction where
    entrySeverity _ = Warning
    helpDoc _ = "warn when a total function is undefined"

instance SQL.Table WarnBottomTotalFunction

warnBottomTotalFunction
    :: MonadLog logger
    => InternalVariable variable
    => TermLike variable
    -> logger ()
warnBottomTotalFunction (mapVariables (fmap toVariable) (fmap toVariable) -> term) =
    logEntry WarnBottomTotalFunction { term }
