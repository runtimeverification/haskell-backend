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
    , unparseGeneric
    , unparse2Generic
    , unparseToText
    , unparseToString
    , renderDefault
    , layoutPrettyUnbounded
    , parameters
    , arguments
    , noArguments
    , attributes
    , unparseToText2
    , unparseToString2
    , parameters2
    , arguments2
    , attributes2
    , parameters'
    , arguments'
    , argument'
    , attributes'
    , escapeString
    , escapeStringT
    , escapeChar
    , escapeCharT
    , unparseAssoc'
    ) where

import qualified Data.Char as Char
import Data.Functor.Const
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc hiding
    ( list
    )
import Data.Text.Prettyprint.Doc.Render.String
    ( renderString
    )
import Data.Text.Prettyprint.Doc.Render.Text
    ( renderStrict
    )
import Data.Void
import Generics.SOP
import qualified GHC.Stack as GHC
import qualified Numeric

{- | Class of types that can be rendered in concrete Kore syntax.

@Unparse@ should only be instantiated for types with a corresponding
concrete syntax, i.e. each instance of @Unparse@ should correspond to a
parser in "Kore.Parser.Parser".

 -}
class Unparse p where
    -- | Render a type from abstract to concrete Kore syntax.
    unparse :: p -> Doc ann
    -- | Render a type from abstract to concrete Applicative Kore syntax.
    unparse2 :: p -> Doc ann

instance Unparse a => Unparse (Const a child) where
    unparse (Const a) = unparse a
    unparse2 (Const a) = unparse2 a


instance Unparse Void where
    unparse = \case {}
    unparse2 = \case {}

{- | Unparse a 'Generic' type with 'unparse'.

/All/ arguments of /all/ constructors must be instances of 'Unparse'; this is
the @'All2' 'Unparse'@ constraint.

Each constructor is unparsed in the following generic way:

- For zero-argument constructors, produce no output ('empty').
- For one-argument constructors, 'unparse' the argument.
- For construtors with more arguments, 'unparse' each argument and combine them
  with 'sep'.

@unparseGeneric@ can be used to quickly implement 'unparse' for types that are
instances of 'Generic'. @unparseGeneric@ is not the default implementation for
all types because it is /excessively/ general. Instances that rely on
@unparseGeneric@ and @unparse2Generic@ should test that these functions
implement the desired behavior, i.e. that they actually produce output that can
be parsed.

See also: 'unparse2Generic'

 -}
unparseGeneric :: (Generic a, All2 Unparse (Code a)) => a -> Doc ann
unparseGeneric = unparseGenericWith unparse
{-# INLINE unparseGeneric #-}

{- | Unparse a 'Generic' type with 'unparse2'.

@unparse2Generic@ is exactly the same as @unparseGeneric@, but uses 'unparse2'
instead of 'unparse'.

 -}
unparse2Generic :: (Generic a, All2 Unparse (Code a)) => a -> Doc ann
unparse2Generic = unparseGenericWith unparse2
{-# INLINE unparse2Generic #-}

unparseGenericWith
    :: (Generic a, All2 Unparse (Code a))
    => (forall x. Unparse x => x -> Doc ann)  -- ^ function to unparse anything
    -> a
    -> Doc ann
unparseGenericWith helper =
    sep . hcollapse . hcmap constraint (mapIK helper) . from
  where
    constraint = Proxy :: Proxy Unparse
{-# INLINE unparseGenericWith #-}

-- | Serialize an object to 'Text'.
unparseToText :: Unparse p => p -> Text
unparseToText = renderStrict . layoutPretty defaultLayoutOptions . unparse

unparseToText2 :: Unparse p => p -> Text
unparseToText2 = renderStrict . layoutPretty defaultLayoutOptions . unparse2

-- | Serialize an object to 'String'.
unparseToString :: Unparse p => p -> String
unparseToString = renderDefault . unparse

unparseToString2 :: Unparse p => p -> String
unparseToString2 = renderDefault . unparse2

renderDefault :: Doc ann -> String
renderDefault = renderString . layoutPretty defaultLayoutOptions

parameters :: Unparse p => [p] -> Doc ann
parameters = parameters' . map unparse

parameters2 :: Unparse p => [p] -> Doc ann
parameters2 = parameters2' . map unparse2

-- | Print a list of sort parameters.
parameters' :: [Doc ann] -> Doc ann
parameters' = list lbrace rbrace
parameters2' :: [Doc ann] -> Doc ann
parameters2' = list2 "" ""

arguments :: Unparse p => [p] -> Doc ann
arguments = arguments' . map unparse

arguments2 :: Unparse p => [p] -> Doc ann
arguments2 = arguments2' . map unparse2

-- | Print a list of documents as arguments.
arguments' :: [Doc ann] -> Doc ann
arguments' = list lparen rparen
arguments2' :: [Doc ann] -> Doc ann
arguments2' = list2 "" ""

-- | Print a document as arguments.
argument' :: Doc ann -> Doc ann
argument' = list lparen rparen . (: [])


-- | Print a list of no arguments.
noArguments :: Doc ann
noArguments = arguments' []

attributes :: Unparse p => [p] -> Doc ann
attributes = attributes' . map unparse

attributes2 :: Unparse p => [p] -> Doc ann
attributes2 = attributes' . map unparse2

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
        xs ->
            (group . (<> close) . nest 4 . (open <>) . vsep . punctuate between)
                xs
  where
    open = left <> line'
    close = line' <> right
    between = comma

-- | Print a list of documents separated by space in the preferred Kore format.
list2
    :: Doc ann  -- ^ opening list delimiter
    -> Doc ann  -- ^ closing list delimiter
    -> [Doc ann]  -- ^ list items
    -> Doc ann
list2 left right =
    \case
        [] -> left <> right
        xs ->
            (group . (<> close) . nest 4 . (open <>) . vsep . punctuate between)
                xs
  where
    open = left <> line'
    close = line' <> right
    between = space


-- | Render a 'Doc ann' with indentation and without extra line breaks.
layoutPrettyUnbounded :: Doc ann -> SimpleDocStream ann
layoutPrettyUnbounded =
    layoutPretty LayoutOptions { layoutPageWidth = Unbounded }

{- | Escape a 'String' for a Kore string literal.

@escapeString@ does not include the surrounding delimiters.

 -}
escapeString :: String -> String
escapeString s = foldr escapeCharS "" s

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

{- | Unparse an associative binary operator applied to many arguments.

@unparseAssoc'@ avoids creeping indentation.

 -}
unparseAssoc'
    :: GHC.HasCallStack
    => Doc ann    -- ^ pattern head
    -> Doc ann    -- ^ identity element
    -> [Doc ann]  -- ^ arguments
    -> Doc ann
unparseAssoc' oper ident =
    worker
  where
    worker [ ] = ident
    worker [x] = x
    worker (x:xs) =
        mconcat
            ( worker' x xs
            : line'
            : replicate (length xs) rparen
            )

    worker' x [] = indent 4 x
    worker' x (y:rest) =
        mconcat
            [ oper <> lparen <> line'
            , indent 4 x <> comma <> line
            , worker' y rest
            ]
