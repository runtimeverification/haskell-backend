module CString
       ( unescapeCString
       , oneCharEscapeDict
       ) where

import CharSet

import Data.Char (isOctDigit, isHexDigit, chr, toUpper, digitToInt)

oneCharEscapeDict :: CharSet
oneCharEscapeDict = CharSet.make "'\"?\\abfnrtv"

joinChar :: Char -> Either String String -> Either String String
joinChar c (Right str) = Right (c:str)
joinChar _ error = error

joinString :: String -> Either String String -> Either String String
joinString prefix (Right str) = Right (prefix ++ str)
joinString _ error = error

{-|Expects input string to be a properly escaped C String.
-}
unescapeCString :: String -> Either String String
unescapeCString "" = Right ""
unescapeCString ('\\':cs) = unescapePrefixAndContinue cs
unescapeCString (c:cs) = joinChar c (unescapeCString cs)

unescapePrefixAndContinue :: String -> Either String String
unescapePrefixAndContinue (c:cs)
  | c `CharSet.elem` oneCharEscapeDict =
      joinChar (unescapeOne c) (unescapeCString cs)
  | isOctDigit c =
      let (octs,rest) = span isOctDigit cs
          (digits, octs') = splitAt 2 octs
          octVal = digitsToNumber 8 (c:digits)
      in joinString (chr octVal : octs') (unescapeCString rest)
  | c == 'x' =
      let (hexes,rest) = span isHexDigit cs
          hexVal = digitsToNumber 16 hexes
      in joinChar (chr hexVal) (unescapeCString rest)
  | toUpper c == 'U' =
      let digitCount = if c == 'u' then 4 else 8
          (unis, rest) = splitAt digitCount cs
          hexVal = digitsToNumber 16 unis
      in if digitCount == length unis
          then joinChar (chr hexVal) (unescapeCString rest)
          else Left "Invalid unicde sequence length."
unescapePrefixAndContinue cs =
  Left ("unescapeCString : Unknown escape sequence '\\" ++ cs ++ "'.")

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
