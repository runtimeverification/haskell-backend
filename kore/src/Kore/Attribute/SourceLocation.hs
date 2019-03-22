{-|
Module      : Kore.Attribute.SourceLocation
Description : Source and location attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Attribute.SourceLocation
    ( SourceLocation (..)
    , Source (..)
    , Location (..)
    ) where

import           Control.DeepSeq
                 ( NFData )
import           Control.Monad
                 ( (>=>) )
import           Data.Default
import           Data.Text.Prettyprint.Doc
                 ( Pretty )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import qualified Control.Lens.TH.Rules as Lens
import           Kore.Attribute.Location
                 ( LineColumn (..), Location (..) )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import           Kore.Attribute.Source
                 ( Source (..) )

data SourceLocation = SourceLocation
    { location :: !Location
    , source   :: !Source
    } deriving (Eq, Ord, Show, Generic)

Lens.makeLenses ''SourceLocation

instance NFData SourceLocation

instance Default SourceLocation where
    def = SourceLocation def def

instance ParseAttributes SourceLocation where
    parseAttribute attr =
            lensLocation (parseAttribute attr)
            >=> lensSource (parseAttribute attr)

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
