module KoreLexeme
       ( colonParser
       , commaParser
       , curlyPairParser
       , idParser
       , inCurlyBracesParser
       , inParenthesesParser
       , inSquareBracketsParser
       , keywordBasedParsers
       , mlLexemeParser
       , moduleNameParser
       , parenPairParser
       , skipWhitespace
       , stringLiteralParser
       ) where

import qualified CharDict
import           CharSet
import           CString
import           KoreAST

import           Control.Applicative              ((<|>))
import           Control.Monad                    (void)
import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8
import           Data.Char                        (isHexDigit, isOctDigit)

idParser :: Parser Id
idParser = lexeme idRawParser

stringLiteralParser :: Parser StringLiteral
stringLiteralParser = lexeme stringLiteralRawParser

moduleNameParser :: Parser ModuleName
moduleNameParser = lexeme moduleNameRawParser

data CommentScannerState = COMMENT | STAR | END

multiLineCommentToken :: Parser ()
multiLineCommentToken = do
    void (Parser.string (Char8.pack "/*"))
    comment <- Parser.scan COMMENT delta
    if Char8.length comment < 2 then fail "Unfinished comment (short)."
    else if Char8.last comment /= '/' then fail "Unfinished comment (/)."
    else if Char8.last (Char8.init comment) /= '*'
        then fail "Unfinished comment (*)."
        else return ()
  where
    delta END _    = Nothing
    delta _ '*'    = Just STAR
    delta STAR '/' = Just END
    delta _ _      = Just COMMENT

singleLineCommentToken :: Parser ()
singleLineCommentToken = do
    void (Parser.string (Char8.pack "//"))
    void (Parser.scan COMMENT delta)
  where
    delta END _  = Nothing
    delta _ '\n' = Just END
    delta _ _    = Just COMMENT

whitespaceChunk :: Parser ()
whitespaceChunk
      = multiLineCommentToken
    <|> singleLineCommentToken
    <|> (Parser.space *> Parser.skipSpace)

-- TODO: Rewrite this, or parts of this, using Parser.scan
skipWhitespace :: Parser ()
skipWhitespace = Parser.skipMany whitespaceChunk

lexeme :: Parser a -> Parser a
lexeme p = p <* skipWhitespace

genericIdParser :: CharSet -> CharSet -> (String -> a) -> Parser a
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

moduleNameRawParser :: Parser ModuleName
moduleNameRawParser =
  genericIdParser moduleNameFirstCharSet moduleNameCharSet ModuleName

idFirstCharSet :: CharSet
idFirstCharSet = CharSet.make (['A'..'Z'] ++ ['a'..'z'])

idCharSet :: CharSet
idCharSet = CharSet.join idFirstCharSet (CharSet.make (['0'..'9'] ++ "'"))

objectIdParser :: Parser Id
objectIdParser = genericIdParser idFirstCharSet idCharSet Id

metaIdParser :: Parser Id
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

idRawParser :: Parser Id
idRawParser = metaIdParser <|> objectIdParser

data StringScannerState = STRING | ESCAPE | HEX StringScannerState

stringLiteralRawParser :: Parser StringLiteral
stringLiteralRawParser = do
    void (Parser.char '"')
    s <- Parser.scan STRING delta
    void (Parser.char '"')
    case unescapeCString (Char8.unpack s) of
        Left e   -> fail e
        Right s' -> return (StringLiteral s')
  where
    pow _ 0 = id
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

tokenCharParser :: Char -> Parser ()
tokenCharParser c = lexeme (void (Parser.char c))

colonParser :: Parser ()
colonParser = tokenCharParser ':'

openCurlyBraceParser :: Parser ()
openCurlyBraceParser = tokenCharParser '{'

closedCurlyBraceParser :: Parser ()
closedCurlyBraceParser = tokenCharParser '}'

inCurlyBracesParser :: Parser a -> Parser a
inCurlyBracesParser p =
    openCurlyBraceParser *> p <* closedCurlyBraceParser

openParenthesisParser :: Parser ()
openParenthesisParser = tokenCharParser '('

closedParenthesisParser :: Parser ()
closedParenthesisParser = tokenCharParser ')'

inParenthesesParser :: Parser a -> Parser a
inParenthesesParser p =
    openParenthesisParser *> p <* closedParenthesisParser

rawPairParser :: Parser a -> Parser b -> Parser (a,b)
rawPairParser pa pb = do
    a <- pa
    commaParser
    b <- pb
    return (a, b)

parenPairParser :: Parser a -> Parser b -> Parser (a,b)
parenPairParser pa pb = inParenthesesParser (rawPairParser pa pb)

curlyPairParser :: Parser a -> Parser b -> Parser (a,b)
curlyPairParser pa pb = inCurlyBracesParser (rawPairParser pa pb)

openSquareBracketParser :: Parser ()
openSquareBracketParser = tokenCharParser '['

closedSquareBracketParser :: Parser ()
closedSquareBracketParser = tokenCharParser ']'

inSquareBracketsParser :: Parser a -> Parser a
inSquareBracketsParser p =
    openSquareBracketParser *> p <* closedSquareBracketParser

commaParser :: Parser ()
commaParser = tokenCharParser ','

mlLexemeParser :: String -> Parser ()
mlLexemeParser s = lexeme (void (Parser.string (Char8.pack s)))

keywordBasedParsers :: [(String, Parser a)] -> Parser a
keywordBasedParsers [] = fail "Keyword Based Parsers - no parsers"
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
            then fail "Keyword Based Parsers - unexpected character."
            else Parser.char c *> keywordBasedParsers ts
    dict = CharDict.memoize tailParser


