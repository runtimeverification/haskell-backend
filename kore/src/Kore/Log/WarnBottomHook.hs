{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.WarnBottomHook
    ( WarnBottomHook (..)
    , warnBottomHook
    ) where

import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Database.SQLite.Simple as SQLite
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

instance SQL.Table WarnBottomHook where
    createTable conn proxy = do
        SQLite.execute_ conn $ SQLite.Query $ Text.unwords
            [ "CREATE TABLE IF NOT EXISTS"
            , (Text.pack . quoted) qualifiedName
            , "(id INTEGER PRIMARY KEY, hook TEXT NOT NULL, term TEXT NOT NULL)"
            ]
      where
        info = SOP.datatypeInfo proxy
        quoted str = "\"" ++ str ++ "\""
        qualifiedName = SOP.moduleName info <> "." <> SOP.datatypeName info

warnBottomHook
    :: MonadLog logger
    => SimplifierVariable variable
    => Text
    -> TermLike variable
    -> logger ()
warnBottomHook hook (mapVariables toVariable -> term) =
    logM WarnBottomHook { hook, term }
