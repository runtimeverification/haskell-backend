{-|
Module      : Kore.Unparser
Description : Render abstract to concrete Kore syntax
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unparser
    ( Unparse (..)
    , unparseToText
    , unparseToString
    , renderDefault
    , layoutPrettyUnbounded
    , parameters
    , arguments
    , noArguments
    , attributes
    , parameters'
    , arguments'
    , attributes'
    , escapeString
    , escapeStringT
    , escapeChar
    , escapeCharT
    ) where

import qualified Data.Char as Char
import           Data.Functor.Const
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           Data.Text.Prettyprint.Doc hiding
                 ( list )
import           Data.Text.Prettyprint.Doc.Render.String
                 ( renderString )
import           Data.Text.Prettyprint.Doc.Render.Text
                 ( renderStrict )
import           Data.Void
import qualified Numeric

{- | Class of types that can be rendered in concrete Kore syntax.

    @Unparse@ should only be instantiated for types with a corresponding
    concrete syntax, i.e. each instance of @Unparse@ should correspond to a
    parser in "Kore.Parser.Parser".

    @Unparse@ assumes that the pattern is fully externalized by
    'Builtin.externalizePattern'. An error will be thrown if an internal domain
    value is found.

 -}
class Unparse p where
    -- | Render a type from abstract to concrete Kore syntax.
    unparse :: p -> Doc ann

instance Unparse a => Unparse (Const a child) where
    unparse (Const a) = unparse a

instance Unparse Void where
    unparse = \case {}

-- | Serialize an object to 'Text'.
unparseToText :: Unparse p => p -> Text
unparseToText = renderStrict . layoutPretty defaultLayoutOptions . unparse

-- | Serialize an object to 'String'.
unparseToString :: Unparse p => p -> String
unparseToString = renderDefault . unparse

renderDefault :: Doc ann -> String
renderDefault = renderString . layoutPretty defaultLayoutOptions

parameters :: Unparse p => [p] -> Doc ann
parameters = parameters' . map unparse

-- | Print a list of sort parameters.
parameters' :: [Doc ann] -> Doc ann
parameters' = list lbrace rbrace

arguments :: Unparse p => [p] -> Doc ann
arguments = arguments' . map unparse

-- | Print a list of documents as arguments.
arguments' :: [Doc ann] -> Doc ann
arguments' = list lparen rparen

-- | Print a list of no arguments.
noArguments :: Doc ann
noArguments = arguments' []

attributes :: Unparse p => [p] -> Doc ann
attributes = attributes' . map unparse

-- | Print a list of documents as attributes.
attributes' :: [Doc ann] -> Doc ann
attributes' = list lbracket rbracket

-- | Print a list of documents separated by commas in the preferred Kore format.
list
    :: Doc ann  -- ^ opening list delimiter
    -> Doc ann  -- ^ closing list delimiter
    -> [Doc ann]  -- ^ list items
    -> Doc ann
list left right =
    \case
        [] -> left <> right
        xs -> (group . (<> close) . nest 4 . (open <>) . vsep . punctuate between) xs
  where
    open = left <> line'
    close = line' <> right
    between = comma

-- | Render a 'Doc ann' with indentation and without extra line breaks.
layoutPrettyUnbounded :: Doc ann -> SimpleDocStream ann
layoutPrettyUnbounded = layoutPretty LayoutOptions { layoutPageWidth = Unbounded }

{- | Escape a 'String' for a Kore string literal.

@escapeString@ does not include the surrounding delimiters.

 -}
escapeString :: String -> String
escapeString s = foldr (.) id (map escapeCharS s) ""

escapeStringT :: Text -> Text
escapeStringT = Text.concatMap escapeCharT

{- | Escape a 'Char' for a Kore character literal.

@escapeChar@ does not include the surrounding delimiters.

 -}
escapeChar :: Char -> String
escapeChar c = escapeCharS c ""

escapeCharS :: Char -> ShowS
escapeCharS c
  | c >= '\x20' && c < '\x7F' =
    case Map.lookup c oneCharEscapes of
        Nothing ->
            -- printable 7-bit ASCII
            showChar c
        Just esc ->
            -- single-character escape sequence
            showChar '\\' . showChar esc
  | c < '\x100'   = showString "\\x" . zeroPad 2 (showHexCode c)
  | c < '\x10000' = showString "\\u" . zeroPad 4 (showHexCode c)
  | otherwise     = showString "\\U" . zeroPad 8 (showHexCode c)
  where
    showHexCode = Numeric.showHex . Char.ord
    zeroPad = padLeftWithCharToLength '0'

escapeCharT :: Char -> Text
escapeCharT c
  | c >= '\x20' && c < '\x7F' =
    case Map.lookup c oneCharEscapes of
        Nothing ->
            -- printable 7-bit ASCII
            Text.singleton c
        Just esc ->
            -- single-character escape sequence
            "\\" <> Text.singleton esc
  | c < '\x100'   = "\\x" <> zeroPad 2 (Text.pack $ showHexCode c "")
  | c < '\x10000' = "\\u" <> zeroPad 4 (Text.pack $ showHexCode c "")
  | otherwise     = "\\U" <> zeroPad 8 (Text.pack $ showHexCode c "")
  where
    showHexCode = Numeric.showHex . Char.ord
    zeroPad i = Text.justifyRight i '0'


padLeftWithCharToLength :: Char -> Int -> ShowS -> ShowS
padLeftWithCharToLength c i ss =
    showString (replicate (i - length (ss "")) c) . ss

oneCharEscapes :: Map Char Char
oneCharEscapes =
    Map.fromList
        [ ('\\', '\\')
        , ('"', '"')
        , ('\f', 'f')
        , ('\n', 'n')
        , ('\r', 'r')
        , ('\t', 't')
        ]
