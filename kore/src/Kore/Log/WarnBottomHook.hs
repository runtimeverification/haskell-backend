{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.WarnBottomHook
    ( WarnBottomHook (..)
    , warnBottomHook
    ) where

import Prelude.Kore

import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import GHC.Generics as GHC

import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    )
import Kore.Unparser
    ( unparse
    )
import Log
import qualified SQL

data WarnBottomHook =
    WarnBottomHook
        { hook :: !Text
        , term :: !(TermLike Variable)
        }
    deriving (GHC.Generic)

instance SOP.Generic WarnBottomHook

instance SOP.HasDatatypeInfo WarnBottomHook

instance Pretty WarnBottomHook where
    pretty WarnBottomHook { hook, term } =
        Pretty.vsep
            [ "Evaluating "
                <> Pretty.squotes (Pretty.pretty hook)
                <> " in pattern:"
            , Pretty.indent 4 (unparse term)
            , "has resulted in \\bottom."
            ]

instance Entry WarnBottomHook where
    entrySeverity _ = Warning

instance SQL.Table WarnBottomHook

warnBottomHook
    :: MonadLog logger
    => SimplifierVariable variable
    => Text
    -> TermLike variable
    -> logger ()
warnBottomHook hook (mapVariables (fmap toVariable) (fmap toVariable) -> term) =
    logM WarnBottomHook { hook, term }
