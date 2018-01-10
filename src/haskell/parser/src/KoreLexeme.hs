module KoreLexeme
       ( closedCurlyBraceParser
       , closedParenthesisParser
       , closedSquareBracketParser
       , colonParser
       , commaParser
       , idParser
       , keywordBasedParsers
       , mlLexemeParser
       , moduleNameParser
       , openCurlyBraceParser
       , openParenthesisParser
       , openSquareBracketParser
       , skipWhitespace
       , stringLiteralParser
       ) where

import qualified CharDict
import           CharSet
import           CString
import           KoreAST

import           Control.Applicative
import           Control.Monad
import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8
import           Data.Char
import           Data.List (nub)

idParser :: Parser.Parser Id
idParser = lexeme idRawParser

stringLiteralParser :: Parser.Parser StringLiteral
stringLiteralParser = lexeme stringLiteralRawParser

data CommentScannerState = COMMENT | STAR | END

multiLineCommentToken :: Parser.Parser ()
multiLineCommentToken = do
    void (Parser.string (Char8.pack "/*"))
    void (Parser.scan COMMENT delta)
  where
    delta END _    = Nothing
    delta _ '*'    = Just STAR
    delta STAR '/' = Just END
    delta _ _      = Just COMMENT

singleLineCommentToken :: Parser.Parser ()
singleLineCommentToken = do
    void (Parser.string (Char8.pack "//"))
    void (Parser.scan COMMENT delta)
  where
    delta END _  = Nothing
    delta _ '\n' = Just END
    delta _ _    = Just COMMENT

whitespaceChunk :: Parser.Parser ()
whitespaceChunk
      = multiLineCommentToken
    <|> singleLineCommentToken
    <|> (Parser.space *> Parser.skipSpace)

-- TODO: Rewrite this, or parts of this, using Parser.scan
skipWhitespace :: Parser.Parser ()
skipWhitespace = Parser.skipMany whitespaceChunk

lexeme :: Parser.Parser a -> Parser.Parser a
lexeme p = p <* skipWhitespace

genericIdParser :: CharSet -> CharSet -> (String -> a) -> Parser.Parser a
genericIdParser firstCharSet charSet constructor = do
    c <- Parser.peekChar'
    id <- if not (c `CharSet.elem` firstCharSet)
        then fail "genericidParser"
        else Parser.takeWhile (`CharSet.elem` charSet)
    return (constructor (Char8.unpack id))

moduleNameFirstCharSet :: CharSet
moduleNameFirstCharSet = CharSet.make ['A'..'Z']

moduleNameCharSet :: CharSet
moduleNameCharSet =
  CharSet.join moduleNameFirstCharSet (CharSet.make (['0'..'9'] ++ "-"))

moduleNameParser :: Parser.Parser ModuleName
moduleNameParser =
  genericIdParser moduleNameFirstCharSet moduleNameCharSet ModuleName

idFirstCharSet :: CharSet
idFirstCharSet = CharSet.make (['A'..'Z'] ++ ['a'..'z'])

idCharSet :: CharSet
idCharSet = CharSet.join idFirstCharSet (CharSet.make (['0'..'9'] ++ "'"))

objectIdParser :: Parser.Parser Id
objectIdParser = genericIdParser idFirstCharSet idCharSet Id

metaIdParser :: Parser.Parser Id
metaIdParser = do
    c <- Parser.char '#'
    c' <- Parser.peekChar'
    if (c' == '`')
        then do
            void (Parser.char c')
            Id id <- objectIdParser
            return (Id (c:c':id))
        else do
            Id id <- objectIdParser
            return (Id (c:id))

idRawParser :: Parser.Parser Id
idRawParser = metaIdParser <|> objectIdParser

data StringScannerState = STRING | ESCAPE | HEX StringScannerState

stringLiteralRawParser :: Parser.Parser StringLiteral
stringLiteralRawParser = do
    void (Parser.char '"')
    s <- Parser.scan STRING delta
    void (Parser.char '"')
    let s' = unescapeCString (Char8.unpack s)
    return (StringLiteral s')
  where
    pow f 0 = id
    pow f n = f . pow f (n-1)
    delta STRING '"' = Nothing
    delta STRING '\\' = Just ESCAPE
    delta STRING _ = Just STRING
    delta ESCAPE c
      | c `CharSet.elem` oneCharEscapeDict = Just STRING
      | isOctDigit c = Just STRING -- ingore actual codes for now
      | c == 'x' = Just (HEX STRING)
      | c == 'u' = Just ((pow HEX 4) STRING)
      | c == 'U' = Just ((pow HEX 8) STRING)
      | otherwise = Nothing
    delta (HEX s) c
      | isHexDigit c = Just s
      | otherwise = Nothing

tokenCharParser :: Char -> Parser.Parser ()
tokenCharParser c = lexeme (void (Parser.char c))

colonParser :: Parser.Parser ()
colonParser = tokenCharParser ':'

openCurlyBraceParser :: Parser.Parser ()
openCurlyBraceParser = tokenCharParser '{'

closedCurlyBraceParser :: Parser.Parser ()
closedCurlyBraceParser = tokenCharParser '}'

openParenthesisParser :: Parser.Parser ()
openParenthesisParser = tokenCharParser '('

closedParenthesisParser :: Parser.Parser ()
closedParenthesisParser = tokenCharParser ')'

openSquareBracketParser :: Parser.Parser ()
openSquareBracketParser = tokenCharParser '['

closedSquareBracketParser :: Parser.Parser ()
closedSquareBracketParser = tokenCharParser ']'

commaParser :: Parser.Parser ()
commaParser = tokenCharParser ','

mlLexemeParser :: String -> Parser.Parser ()
mlLexemeParser s = lexeme (void (Parser.string (Char8.pack s)))

keywordBasedParsers :: [(String, Parser.Parser a)] -> Parser.Parser a
keywordBasedParsers [] = fail "Keyword Based Parsers"
keywordBasedParsers [(k, p)] = mlLexemeParser k *> p
keywordBasedParsers stringParsers = do
    c <- Parser.peekChar'
    dict CharDict.! c
  where
    tails c =
        [(tail prefix, p) | (prefix, p) <- stringParsers, head prefix == c]
    tailParser c =
        let ts = tails c
        in if null ts
            then fail "Keyword Based Parsers"
            else Parser.char c *> keywordBasedParsers ts
    dict = CharDict.memoize tailParser


