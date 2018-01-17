module KoreLexemeImpl where

import qualified CharDict
import           CharSet
import           CString
import           KoreAST

import           Control.Monad                    (void, when)
import qualified Data.Attoparsec.ByteString       as BParser (runScanner)
import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8
import           Data.Char                        (isHexDigit, isOctDigit)
import           Data.Maybe                       (isJust)
import qualified Data.Trie                        as Trie

idParser :: IsMeta a => a -> Parser (Id a)
idParser x = Id <$> lexeme (idRawParser x)

stringLiteralParser :: Parser StringLiteral
stringLiteralParser = lexeme stringLiteralRawParser

moduleNameParser :: Parser ModuleName
moduleNameParser = lexeme moduleNameRawParser

data CommentScannerState = COMMENT | STAR | END

multiLineCommentToken :: Parser ()
multiLineCommentToken = do
    (_,state) <- BParser.runScanner COMMENT delta'
    case state of
        END -> return ()
        _   -> fail "Unfinished comment."
  where
    delta' s c = delta s (toEnum (fromEnum c))
    delta END _    = Nothing
    delta _ '*'    = Just STAR
    delta STAR '/' = Just END
    delta _ _      = Just COMMENT

singleLineCommentToken :: Parser ()
singleLineCommentToken =
    void (Parser.scan COMMENT delta)
  where
    delta END _  = Nothing
    delta _ '\n' = Just END
    delta _ _    = Just COMMENT


spaceChars :: [Char]
spaceChars = [' ', '\t', '\n', '\v', '\f', '\r']

whitespaceChunk :: Parser ()
whitespaceChunk =
    prefixBasedParsersWithDefault
        stringParser
        (return ())
        (
            [ ("/*", multiLineCommentToken *> whitespaceChunk)
            , ("//", singleLineCommentToken *> whitespaceChunk)
            ]
            ++
            map (\c -> ([c], Parser.skipSpace *> whitespaceChunk)) spaceChars
        )

-- TODO: Rewrite this, or parts of this, using Parser.scan
skipWhitespace :: Parser ()
skipWhitespace = whitespaceChunk

lexeme :: Parser a -> Parser a
lexeme p = p <* skipWhitespace

koreKeywordsSet :: Trie.Trie ()
koreKeywordsSet = Trie.fromList $ map (\s -> (Char8.pack s, ()))
    ["module", "endmodule", "sort", "symbol", "alias", "axiom"]

genericIdParser :: CharSet -> CharSet -> Parser String
genericIdParser firstCharSet charSet = do
    c <- Parser.peekChar'
    idChar <- if not (c `CharSet.elem` firstCharSet)
        then fail ("genericidParser: Invalid first character '" ++ c : "'.")
        else Parser.takeWhile (`CharSet.elem` charSet)
    let identifier = Char8.unpack idChar
    when (isJust $ Trie.lookup idChar koreKeywordsSet)
        (fail ("Identifiers should not be keywords: '" ++ identifier ++ "'."))
    return identifier

moduleNameFirstCharSet :: CharSet
moduleNameFirstCharSet = idFirstCharSet

moduleNameCharSet :: CharSet
moduleNameCharSet = idCharSet

moduleNameRawParser :: Parser ModuleName
moduleNameRawParser =
  ModuleName <$> genericIdParser moduleNameFirstCharSet moduleNameCharSet

idFirstCharSet :: CharSet
idFirstCharSet = CharSet.make (['A'..'Z'] ++ ['a'..'z'])

idCharSet :: CharSet
idCharSet = CharSet.join idFirstCharSet (CharSet.make (['0'..'9'] ++ "'-"))

objectIdRawParser :: Parser String
objectIdRawParser = genericIdParser idFirstCharSet idCharSet

metaIdRawParser :: Parser String
metaIdRawParser = do
    c <- Parser.char '#'
    c' <- Parser.peekChar'
    if c' == '`'
        then do
            void (Parser.char c')
            idToken <- objectIdRawParser
            return (c:c':idToken)
        else do
            idToken <- objectIdRawParser
            return (c:idToken)

idRawParser :: (IsMeta a) => a -> Parser String
idRawParser x = case metaType x of
    ObjectType -> objectIdRawParser
    MetaType   -> metaIdRawParser

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
    openCurlyBraceParser *> inCurlyBracesRemainderParser p

inCurlyBracesRemainderParser :: Parser a -> Parser a
inCurlyBracesRemainderParser p =
    p <* closedCurlyBraceParser

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

curlyPairRemainderParser :: Parser a -> Parser (a,a)
curlyPairRemainderParser pa = inCurlyBracesRemainderParser (rawPairParser pa pa)

openSquareBracketParser :: Parser ()
openSquareBracketParser = tokenCharParser '['

closedSquareBracketParser :: Parser ()
closedSquareBracketParser = tokenCharParser ']'

inSquareBracketsParser :: Parser a -> Parser a
inSquareBracketsParser p =
    openSquareBracketParser *> p <* closedSquareBracketParser

commaParser :: Parser ()
commaParser = tokenCharParser ','

stringParser :: String -> Parser ()
stringParser = void . Parser.string . Char8.pack

mlLexemeParser :: String -> Parser ()
mlLexemeParser s =
    lexeme (void (Parser.string (Char8.pack s) <* keywordEndParser))

keywordEndParser :: Parser ()
keywordEndParser = do
    mc <- Parser.peekChar
    case mc of
        Nothing -> return ()
        Just c -> if c `CharSet.elem` idCharSet
            then fail "Expecting keyword to end."
            else return ()


keywordBasedParsers :: [(String, Parser a)] -> Parser a
keywordBasedParsers stringParsers =
    prefixBasedParsers mlLexemeParser stringParsers

prefixBasedParsers ::  (String -> Parser ()) ->[(String, Parser a)] -> Parser a
prefixBasedParsers _ [] = error "Keyword Based Parsers - no parsers"
prefixBasedParsers prefixParser [(k, p)] = prefixParser k *> p
prefixBasedParsers prefixParser stringParsers = do
    c <- Parser.peekChar'
    dict CharDict.! c
  where
    tails c =
        [(tail prefix, p) | (prefix, p) <- stringParsers, head prefix == c]
    tailParser c =
        let ts = tails c
        in if null ts
            then fail "Keyword Based Parsers - unexpected character."
            else Parser.char c *> prefixBasedParsers prefixParser ts
    dict = CharDict.memoize tailParser

prefixBasedParsersWithDefault
    :: (String -> Parser ()) -> Parser a -> [(String, Parser a)] -> Parser a
prefixBasedParsersWithDefault _ _ [] =
    error "Keyword Based Parsers With Default - no parsers"
prefixBasedParsersWithDefault prefixParser defaultParser stringParsers = do
    mc <- Parser.peekChar
    case mc of
        Nothing -> defaultParser
        Just c -> if any ((==c).head.fst) stringParsers
            then prefixBasedParsers prefixParser stringParsers
            else defaultParser

metaSortTrie :: Trie.Trie MetaSortType
metaSortTrie = Trie.fromList $ map (\s -> (Char8.pack $ show s, s))
    [ CharSort, CharListSort, PatternSort, PatternListSort, SortSort
    , SortListSort, StringSort, SymbolSort, SymbolListSort
    , VariableSort, VariableListSort
    ]

metaSortParser :: String -> Maybe MetaSortType
metaSortParser identifier = Trie.lookup (Char8.pack identifier) metaSortTrie
