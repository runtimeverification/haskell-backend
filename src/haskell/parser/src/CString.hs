module CString
       ( unescapeCString
       , oneCharEscapeDict
       ) where

import CharDict

import Data.Char

oneCharEscapeDict :: CharDict
oneCharEscapeDict = CharDict.make "'\"?\\abfnrtv"

{-|Expects input string to be a properly escaped C String.
-}
unescapeCString :: String -> String
unescapeCString "" = ""
unescapeCString ('\\':cs) = unescapePrefixAndContinue cs
unescapeCString (c:cs) = c:unescapeCString cs

unescapePrefixAndContinue :: String -> String
unescapePrefixAndContinue (c:cs)
  | c `CharDict.elem` oneCharEscapeDict =
    unescapeOne c : unescapeCString cs
  | isOctDigit c =
      let (octs,rest) = span isOctDigit cs
          (digits, octs') = splitAt 2 octs
          octVal = digitsToNumber 8 (c:digits)
      in (chr octVal : octs') ++ unescapeCString rest
  | c == 'x' =
      let (hexes,rest) = span isHexDigit cs
          hexVal = digitsToNumber 16 (c:hexes)
      in chr hexVal : unescapeCString rest
  | toUpper c == 'U' =
      let digitCount = if c == 'u' then 4 else 8
          (unis, rest) = splitAt digitCount cs
          hexVal = digitsToNumber 16 unis
      in chr hexVal : unescapeCString rest
unescapePrefixAndContinue cs =
  error ("unescapeCString : Unknown escape sequence '\\" ++ cs ++ "'.")

unescapeOne :: Char -> Char
unescapeOne '\'' = '\''
unescapeOne '"' = '"'
unescapeOne '\\' = '\\'
unescapeOne '?' = '?'
unescapeOne 'a' = '\a'
unescapeOne 'b' = '\b'
unescapeOne 'f' = '\f'
unescapeOne 'n' = '\n'
unescapeOne 'r' = '\r'
unescapeOne 't' = '\t'
unescapeOne 'v' = '\v'
unescapeOne c = error ("Unexpected escape sequence '``" ++ "c'.")

digitsToNumber :: Int -> String -> Int
digitsToNumber base = foldl (\r ch -> base * r + digitToInt ch) 0
