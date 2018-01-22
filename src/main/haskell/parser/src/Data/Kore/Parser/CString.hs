{-|
Module      : Data.Kore.Parser.CString
Description : Unescaping for C-style strings. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.Parser.CString
       ( unescapeCString
       , oneCharEscapeDict
       ) where

import           Data.Kore.Parser.CharSet as CharSet

import           Data.Char (chr, digitToInt, isHexDigit, isOctDigit, ord,
                            toUpper)

oneCharEscapeDict :: CharSet
oneCharEscapeDict = makeCharSet "'\"?\\abfnrtv"

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
      (:) <$> (unescapeOne c) <*> (unescapeCString cs)
  | isOctDigit c =
      let (octs,rest) = span isOctDigit cs
          (digits, octs') = splitAt 2 octs
          octVal = digitsToNumber 8 (c:digits)
      in ((chr octVal : octs') ++) <$> (unescapeCString rest)
  | c == 'x' =
      let (hexes,rest) = span isHexDigit cs
          hexVal = digitsToNumber 16 hexes
      in (:) <$> (safeChr hexVal) <*> (unescapeCString rest)
  | toUpper c == 'U' =
      let digitCount = if c == 'u' then 4 else 8
          (unis, rest) = splitAt digitCount cs
          hexVal = digitsToNumber 16 unis
      in if digitCount == length unis
          then (:) <$> (safeChr hexVal) <*> (unescapeCString rest)
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
