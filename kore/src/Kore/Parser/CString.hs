{-|
Module      : Kore.Parser.CString
Description : Unescaping for C-style strings. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Parser.CString
       ( unescapeCString
       , escapeCString
       , escapeCStringT
       , oneCharEscapes
       , oneCharEscapeDict
       ) where

import Data.Char
    ( chr
    , digitToInt
    , isHexDigit
    , isOctDigit
    , ord
    , toUpper
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Numeric
    ( showHex
    , showOct
    )

import Kore.Parser.CharSet as CharSet

oneCharEscapes :: [Char]
oneCharEscapes = "'\"?\\abfnrtv"

oneCharEscapeDict :: CharSet
oneCharEscapeDict = makeCharSet oneCharEscapes

escapeCString :: String -> String
escapeCString s = foldr ((.) . escapeAndAddChar) id s ""

escapeCStringT :: Text -> Text
escapeCStringT = Text.concatMap escapeAndAddCharT

padLeftWithCharToLength :: Char -> Int -> ShowS -> ShowS
padLeftWithCharToLength c i ss =
    showString (replicate (i - length (ss "")) c) . ss

escapeAndAddChar :: Char -> ShowS
escapeAndAddChar '"'  = showString "\\\""
escapeAndAddChar '\'' = showString "\\'"
escapeAndAddChar '\\' = showString "\\\\"
escapeAndAddChar '?'  = showString "\\?"
escapeAndAddChar '\a' = showString "\\a"
escapeAndAddChar '\b' = showString "\\b"
escapeAndAddChar '\f' = showString "\\f"
escapeAndAddChar '\n' = showString "\\n"
escapeAndAddChar '\r' = showString "\\r"
escapeAndAddChar '\t' = showString "\\t"
escapeAndAddChar '\v' = showString "\\v"
escapeAndAddChar c
    | code >= 32 && code < 127 = showChar c    -- printable 7-bit ASCII
    | code <= 255 =
        showString "\\" . zeroPad 3 (showOct code)
    | code <= 65535 = showString "\\u" . zeroPad 4 (showHex code)
    | otherwise =  showString "\\U" . zeroPad 8 (showHex code)
  where
    code = ord c
    zeroPad = padLeftWithCharToLength '0'

escapeAndAddCharT :: Char -> Text
escapeAndAddCharT '"'  = "\\\""
escapeAndAddCharT '\'' = "\\'"
escapeAndAddCharT '\\' = "\\\\"
escapeAndAddCharT '?'  = "\\?"
escapeAndAddCharT '\a' = "\\a"
escapeAndAddCharT '\b' = "\\b"
escapeAndAddCharT '\f' = "\\f"
escapeAndAddCharT '\n' = "\\n"
escapeAndAddCharT '\r' = "\\r"
escapeAndAddCharT '\t' = "\\t"
escapeAndAddCharT '\v' = "\\v"
escapeAndAddCharT c
    | code >= 32 && code < 127 = Text.singleton c    -- printable 7-bit ASCII
    | code <= 255 =
        "\\" <> zeroPad 3 (Text.pack $ showOct code "")
    | code <= 65535 = "\\u" <> zeroPad 4 (Text.pack $ showHex code "")
    | otherwise = "\\U" <> zeroPad 8 (Text.pack $ showHex code "")
  where
    code = ord c
    zeroPad i = Text.justifyRight i '0'

{-|Expects input string to be a properly escaped C String.
-}
unescapeCString :: String -> Either String String
unescapeCString ""        = return ""
unescapeCString ('\\':cs) = unescapePrefixAndContinue cs
unescapeCString (c:cs)    = (c :) <$> unescapeCString cs

{-|Transforms a unicode code point into a char, providing an error message
otherwise.
-}
safeChr :: Int -> Either String Char
safeChr i =
    if i <= ord(maxBound::Char)
        then return (chr i)
        else Left ("Character code " ++ show i ++
            " outside of the representable codes.")

{-|Assumes that the previous character was the start of an escape sequence,
i.e. @\@ and continues the unescape of the string.
-}
unescapePrefixAndContinue :: String -> Either String String
unescapePrefixAndContinue (c:cs)
  | c `CharSet.elem` oneCharEscapeDict =
      (:) <$> unescapeOne c <*> unescapeCString cs
  | isOctDigit c =
      let (octs,rest) = span isOctDigit cs
          (digits, octs') = splitAt 2 octs
          octVal = digitsToNumber 8 (c:digits)
      in ((chr octVal : octs') ++) <$> unescapeCString rest
  | c == 'x' =
      let (hexes,rest) = span isHexDigit cs
          hexVal = digitsToNumber 16 hexes
      in (:) <$> safeChr hexVal <*> unescapeCString rest
  | toUpper c == 'U' =
      let digitCount = if c == 'u' then 4 else 8
          (unis, rest) = splitAt digitCount cs
          hexVal = digitsToNumber 16 unis
      in if digitCount == length unis
          then (:) <$> safeChr hexVal <*> unescapeCString rest
          else Left "Invalid unicode sequence length."
unescapePrefixAndContinue cs =
  Left ("unescapeCString : Unknown escape sequence '\\" ++ cs ++ "'.")

{-|Unescapes the provided character.
-}
unescapeOne :: Char -> Either String Char
unescapeOne '\'' = return '\''
unescapeOne '"'  = return '"'
unescapeOne '\\' = return '\\'
unescapeOne '?'  = return '?'
unescapeOne 'a'  = return '\a'
unescapeOne 'b'  = return '\b'
unescapeOne 'f'  = return '\f'
unescapeOne 'n'  = return '\n'
unescapeOne 'r'  = return '\r'
unescapeOne 't'  = return '\t'
unescapeOne 'v'  = return '\v'
unescapeOne c    = Left ("Unexpected escape sequence '``" ++ show c ++ "'.")

{-|String to number conversion.
-}
digitsToNumber :: Int -> String -> Int
digitsToNumber base = foldl (\r ch -> base * r + digitToInt ch) 0
