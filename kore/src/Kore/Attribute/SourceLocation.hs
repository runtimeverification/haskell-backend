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

import           Control.Applicative
                 ( (<|>) )
import           Control.DeepSeq
                 ( NFData )
import           Data.Default
import           Data.Text.Prettyprint.Doc
                 ( Pretty )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import           Kore.Attribute.Location
                 ( LineColumn (..), Location (..) )
import qualified Kore.Attribute.Location as Location
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import           Kore.Attribute.Source
                 ( Source (..) )
import qualified Kore.Attribute.Source as Source

data SourceLocation = SourceLocation
    { location :: !(Maybe Location)
    , source   :: !(Maybe Source)
    } deriving (Eq, Ord, Show, Generic)

instance NFData SourceLocation

instance Default SourceLocation where
    def = SourceLocation Nothing Nothing

instance ParseAttributes SourceLocation where
    parseAttribute patt SourceLocation { location, source } = do
        l <- hasValueAt Location.start <$> parseAttribute patt def
        s <- hasValueAt Source.unSource <$> parseAttribute patt def
        pure
            $ SourceLocation (location <|> l) (source <|> s)
      where
        hasValueAt :: (a -> Maybe b) -> a -> Maybe a
        hasValueAt f a = maybe Nothing (const . Just $ a) $ f a

instance Pretty SourceLocation where
    pretty SourceLocation
        { location = Just (Location
            { start = Just LineColumn { line = startLine, column = startColumn }
            , end = end
            })
        , source = (Just (Source (Just file)))
        }
      = Pretty.hcat $
        [ Pretty.pretty file
        , ":"
        , Pretty.pretty startLine
        , ":"
        , Pretty.pretty startColumn
        ]
        <> case end of
            Nothing -> []
            Just LineColumn { line = endLine, column = endColumn }  ->
                [ "-"
                , Pretty.pretty endLine
                , ":"
                , Pretty.pretty endColumn
                ]
    pretty _ = ""
