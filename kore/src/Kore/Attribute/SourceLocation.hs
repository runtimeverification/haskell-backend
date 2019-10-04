{-|
Module      : Kore.Attribute.SourceLocation
Description : Source and location attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com

-}

module Kore.Attribute.SourceLocation
    ( SourceLocation (..)
    , Source (..)
    , Location (..)
    ) where

import Control.DeepSeq
    ( NFData
    )
import Control.Monad
    ( (>=>)
    )
import Data.Default
import Data.Generics.Product
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Location
    ( LineColumn (..)
    , Location (..)
    )
import Kore.Attribute.Parser
    ( ParseAttributes (..)
    )
import Kore.Attribute.Source
    ( Source (..)
    )
import Kore.Debug

data SourceLocation = SourceLocation
    { location :: !Location
    , source   :: !Source
    } deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic SourceLocation

instance SOP.HasDatatypeInfo SourceLocation

instance Debug SourceLocation

instance Diff SourceLocation

instance NFData SourceLocation

instance Default SourceLocation where
    def = SourceLocation def def

instance ParseAttributes SourceLocation where
    parseAttribute attr =
        typed @Location (parseAttribute attr)
        >=> typed @Source (parseAttribute attr)

    -- TODO (thomas.tuegel): Implement
    toAttributes _ = def

instance Pretty SourceLocation where
    pretty SourceLocation
        { location = Location { start , end }
        , source = (Source (Just file))
        }
      = Pretty.pretty file <> loc

      where
        loc :: Pretty.Doc ann
        loc =
            case start of
                Just lc -> ":" <> prettyLC lc <> maybeLC end
                Nothing -> Pretty.emptyDoc

        prettyLC :: LineColumn -> Pretty.Doc ann
        prettyLC LineColumn { line, column } =
            Pretty.hcat
                [ Pretty.pretty line
                , ":"
                , Pretty.pretty column
                ]

        maybeLC :: Maybe LineColumn -> Pretty.Doc ann
        maybeLC Nothing = Pretty.emptyDoc
        maybeLC (Just elc) = "-" <> prettyLC elc
    pretty _ = ""
