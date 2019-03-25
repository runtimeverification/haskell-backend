{-|
Module      : Kore.Parser.Lexeme
Description : Lexical unit definitions for Kore and simple ways of composing
              parsers. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Conventions used:

1. In various cases we distinguish between @object-@ and @meta-@ versions of an
   element. For this we parametrize the element's type with an @a@ and we
   provide an element of type @a@ to the parser, usually called @x@.

2. The meta versions are identified by the presence of @#@ characters at
   the start of the element.

3. All parsers consume the whitespace after the parsed element and expect no
   whitespace before.
-}
module Kore.Parser.Lexeme
    (
    -- * Parsers
      colonParser
    , commaParser
    , curlyPairParser
    , curlyPairRemainderParser
    , idParser
    , idFirstChars
    , idOtherChars
    , openCurlyBraceParser
    , inCurlyBracesParser
    , inCurlyBracesRemainderParser
    , inParenthesesParser
    , inSquareBracketsParser
    , keywordBasedParsers
    , metaSortConverter
    , mlLexemeParser
    , moduleNameParser
    , parenPairParser
    , skipWhitespace
    , stringLiteralParser
    , charLiteralParser
    -- * Error messages
    , unrepresentableCode
    , illegalSurrogate
    ) where

import           Control.Monad
                 ( void, when )
import           Control.Monad.Combinators
                 ( manyTill, (<|>) )
import qualified Data.ByteString.Char8 as Char8
import qualified Data.Char as Char
import qualified Data.Foldable as Foldable
import           Data.HashMap.Strict
                 ( HashMap )
import qualified Data.HashMap.Strict as HashMap
import           Data.HashSet
                 ( HashSet )
import qualified Data.HashSet as HashSet
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Maybe
import qualified Data.Text as Text
import           Text.Megaparsec
                 ( SourcePos (..), anySingle, eof, getSourcePos, unPos, (<?>) )
import qualified Text.Megaparsec as Parser
import qualified Text.Megaparsec.Char as Parser
import qualified Text.Megaparsec.Char.Lexer as L

import           Kore.AST.Common
import           Kore.AST.Identifier
import           Kore.AST.MetaOrObject
                 ( MetaOrObject (..) )
import           Kore.AST.Sentence
import qualified Kore.Parser.CharDict as CharDict
import           Kore.Parser.CharSet as CharSet
import           Kore.Parser.ParserUtils as ParserUtils
import           Kore.Sort

sourcePosToFileLocation :: SourcePos -> FileLocation
sourcePosToFileLocation
    SourcePos
        { sourceName = name
        , sourceLine = line'
        , sourceColumn = column'
        }
  = FileLocation
    { fileName = name
    , line     = unPos line'
    , column   = unPos column'
    }

{-|'idParser' parses either an @object-identifier@, or a @meta-identifier@.

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
idParser :: MetaOrObject level
         => level  -- ^ Distinguishes between the meta and non-meta elements.
         -> Parser (Id level)
idParser _ = do
    pos <- sourcePosToFileLocation <$> getSourcePos
    name <- lexeme (objectIdRawParser KeywordsForbidden <|> metaIdRawParser)
    return Id
        { getId = Text.pack name
        , idLocation = AstLocationFile pos
        }

{-|'stringLiteralParser' parses a C-style string literal, unescaping it.

Always starts with @"@.
-} {- " -}
stringLiteralParser :: Parser StringLiteral
stringLiteralParser = lexeme stringLiteralRawParser

{-|'charLiteralParser' parses a C-style char literal, unescaping it.

Always starts with @'@.
-}
charLiteralParser :: Parser CharLiteral
charLiteralParser = lexeme charLiteralRawParser

{-|'moduleNameParser' parses a module name.-}
moduleNameParser :: Parser ModuleName
moduleNameParser = lexeme moduleNameRawParser

{-|'lexeme' transforms a raw parser into one that skips the whitespace and any
comments after the parsed element.
-}
lexeme :: Parser a -> Parser a
lexeme = L.lexeme skipWhitespace

{-|'skipWhitespace' skips whitespace and any comments.
-}
skipWhitespace ::  Parser ()
skipWhitespace = L.space Parser.space1 (L.skipLineComment "//") blockComment
  where
    blockComment = Parser.string "/*" >> void (manyTill commentBody (Parser.string "*/"))
    commentBody = anySingle <|> (eof >> fail "Unfinished comment.")

koreKeywordsSet :: HashSet Char8.ByteString
koreKeywordsSet = HashSet.fromList (Char8.pack <$> keywords)
  where
    keywords = ["module", "endmodule", "sort", "symbol", "alias", "axiom"]

data IdKeywordParsing
    = KeywordsPermitted
    | KeywordsForbidden
  deriving (Eq)

{-|'genericIdRawParser' parses for tokens that can be represented as
@⟨prefix-char⟩ ⟨body-char⟩*@. Does not consume whitespace.
-}
genericIdRawParser
    :: CharSet  -- ^ contains the characters allowed for @⟨prefix-char⟩@.
    -> CharSet  -- ^ contains the characters allowed for @⟨body-char⟩@.
    -> IdKeywordParsing
    -> Parser String
genericIdRawParser firstCharSet bodyCharSet idKeywordParsing = do
    c <- peekChar'
    idChar <- if not (c `CharSet.elem` firstCharSet)
        then fail ("genericIdRawParser: Invalid first character '" ++ c : "'.")
        else ParserUtils.takeWhile (`CharSet.elem` bodyCharSet)
    when
        (  (idKeywordParsing == KeywordsForbidden)
        && HashSet.member (Char8.pack idChar) koreKeywordsSet
        )
        (fail
            (  "Identifiers should not be keywords: '"
            ++ idChar
            ++ "'."
            )
        )
    return idChar

moduleNameFirstCharSet :: CharSet
moduleNameFirstCharSet = idFirstCharSet

moduleNameCharSet :: CharSet
moduleNameCharSet = idCharSet


{-|'moduleNameRawParser' parses a @module-name@. Does not consume whitespace.-}
moduleNameRawParser :: Parser ModuleName
moduleNameRawParser =
  ModuleName . Text.pack <$>
    genericIdRawParser
        moduleNameFirstCharSet moduleNameCharSet KeywordsForbidden

{-# ANN idFirstChars ("HLint: ignore Use String" :: String) #-}
idFirstChars :: [Char]
idFirstChars = ['A'..'Z'] ++ ['a'..'z']

idFirstCharSet :: CharSet
idFirstCharSet = CharSet.makeCharSet idFirstChars

{-# ANN idOtherChars ("HLint: ignore Use String" :: String) #-}
idOtherChars :: [Char]
idOtherChars = ['0'..'9'] ++ "'-"

idCharSet :: CharSet
idCharSet =
    CharSet.join idFirstCharSet (CharSet.makeCharSet idOtherChars)

{-|'objectIdRawParser' extracts the string representing an @object-identifier@.
Does not consume whitespace.
-}
objectIdRawParser :: IdKeywordParsing -> Parser String
objectIdRawParser keywordParsing = do
    backslash <- Parser.string "\\" <|> pure ""
    name <- objectNonslashIdRawParser keywordParsing
    pure (backslash ++ name)

objectNonslashIdRawParser :: IdKeywordParsing -> Parser String
objectNonslashIdRawParser =
    genericIdRawParser idFirstCharSet idCharSet

{-|'metaIdRawParser' extracts the string representing a @meta-identifier@.
Does not consume whitespace.

Always starts with @#@
-}
metaIdRawParser :: Parser String
metaIdRawParser = do
    c <- Parser.char '#'
    c' <- peekChar'
    case c' of
        '`' -> do
            void (Parser.char c')
            idToken <- objectNonslashIdRawParser KeywordsPermitted
            return (c:c':idToken)
        _ -> do
            idToken <- objectIdRawParser KeywordsPermitted
            return (c:idToken)

{- | Parse and unescape a Kore string literal.

@stringLiteralRawParser@ does not consume whitespace.

 -}
stringLiteralRawParser :: Parser StringLiteral
stringLiteralRawParser = do
    _ <- Parser.char '"'
    StringLiteral <$> Text.pack <$> Parser.manyTill charParser (Parser.char '"')

{- | Parse and unescape a Kore character literal.

@charLiteralRawParser@ does not consume whitespace.

 -}
charLiteralRawParser :: Parser CharLiteral
charLiteralRawParser = do
    void (Parser.char '\'')
    c <- charParser
    void (Parser.char '\'')
    return (CharLiteral c)

{- | Select printable ASCII characters.

Only printable ASCII characters are valid in the concrete syntax of Kore.

 -}
isAsciiPrint :: Char -> Bool
isAsciiPrint u = Char.isAscii u && Char.isPrint u
{-# INLINE isAsciiPrint #-}

{- | Parse a single printable ASCII character.
 -}
asciiPrintCharParser :: Parser Char
asciiPrintCharParser =
    Parser.label "printable ASCII character" (Parser.satisfy isAsciiPrint)

{- | Parse a single character.

The character may be escaped, in which case the unescaped character is
returned. @charParser@ is used for parsing string and character literals.

 -}
charParser :: Parser Char
charParser = escapeParser <|> asciiPrintCharParser

{- | Map of all recognized escape sequence parsers.

Each parser will be called after @\\@ and the first character of the sequence is
parsed. One-character escape sequence parsers simply return the escaped
character.

 -}
escapeParsers :: Map Char (Parser Char)
escapeParsers =
    Map.fromList
        [ ('"', return '"')
        , ('\\', return '\\')
        , ('f', return '\f')
        , ('n', return '\n')
        , ('r', return '\r')
        , ('t', return '\t')
        , ('x', escapeUnicodeParser 2)
        , ('u', escapeUnicodeParser 4)
        , ('U', escapeUnicodeParser 8)
        ]

{- | Parse a single hexadecimal digit.
 -}
hexDigitParser :: Parser Char
hexDigitParser =
    Parser.satisfy Char.isHexDigit <?> "hexadecimal digit"
{-# INLINE hexDigitParser #-}

{- | Parse (the tail of) a Unicode escape sequence.
 -}
escapeUnicodeParser
    :: Int  -- ^ Length of expected sequence in characters
    -> Parser Char
escapeUnicodeParser n = do
    hs <- sequence (replicate n hexDigitParser)
    let i = Foldable.foldl' (\r h -> 0x10 * r + Char.digitToInt h) 0 hs
    when (i > Char.ord (maxBound :: Char)) $ fail (unrepresentableCode hs)
    let c = Char.chr i
    when (isSurrogate c) $ fail (illegalSurrogate hs)
    return c
{-# INLINE escapeUnicodeParser #-}

unrepresentableCode
    :: String  -- ^ hexadecimal digits of unpresentable code
    -> String
unrepresentableCode hs =
    "code 0x" ++ hs ++ " is outside the representable range"

isSurrogate :: Char -> Bool
isSurrogate c = Char.generalCategory c == Char.Surrogate
{-# INLINE isSurrogate #-}

illegalSurrogate
    :: String  -- ^ hexadecimal digits of unpresentable code
    -> String
illegalSurrogate hs =
    "code 0x" ++ hs ++ " is an illegal surrogate"

{- | Parse an escape sequence.
 -}
escapeParser :: Parser Char
escapeParser =
    Parser.label "escape sequence" $ do
        _ <- Parser.char '\\'
        c <- anySingle
        fromMaybe
            (Parser.empty <?> "escape sequence")
            (Map.lookup c escapeParsers)
{-# INLINE escapeParser #-}

{-|'tokenCharParser' parses a character, skipping any whitespace after.

Note that it does not enforce the existence of whitespace after the character.
-}
tokenCharParser :: Char -> Parser ()
tokenCharParser c = do
      _ <- L.symbol skipWhitespace [c]
      return ()

{-|'colonParser' parses a @:@ character.-}
colonParser :: Parser ()
colonParser = tokenCharParser ':'

{-|'openCurlyBraceParser' parses a @{@ character.-}
openCurlyBraceParser :: Parser ()
openCurlyBraceParser = tokenCharParser '{'

{-|'closedCurlyBraceParser' parses a @}@ character.-}
closedCurlyBraceParser :: Parser ()
closedCurlyBraceParser = tokenCharParser '}'

{-|'inCurlyBracesParser' parses an element surrounded by curly braces.

Always starts with @{@.
-}
inCurlyBracesParser :: Parser a -> Parser a
inCurlyBracesParser p =
    openCurlyBraceParser *> inCurlyBracesRemainderParser p

inCurlyBracesRemainderParser :: Parser a -> Parser a
inCurlyBracesRemainderParser p =
    p <* closedCurlyBraceParser

{-|'openParenthesisParser' parses a @(@ character.-}
openParenthesisParser :: Parser ()
openParenthesisParser = tokenCharParser '('

{-|'closedParenthesisParser' parses a @)@ character.-}
closedParenthesisParser :: Parser ()
closedParenthesisParser = tokenCharParser ')'

{-|'inParenthesesParser' parses an element surrounded by parentheses.

Always starts with @(@.
-}
inParenthesesParser :: Parser a -> Parser a
inParenthesesParser p =
    openParenthesisParser *> p <* closedParenthesisParser

{-|'commaSeparatedPairParser' parses two elements separated by a comma.-}
commaSeparatedPairParser :: Parser a -> Parser b -> Parser (a,b)
commaSeparatedPairParser pa pb = do
    a <- pa
    commaParser
    b <- pb
    return (a, b)

{-|'parenPairParser' parses two elements between parentheses, separated by
a comma.

Always starts with @(@.
-}
parenPairParser :: Parser a -> Parser b -> Parser (a,b)
parenPairParser pa pb = inParenthesesParser (commaSeparatedPairParser pa pb)

{-|'curlyPairParser' parses two elements between curly braces, separated by
a comma.

Always starts with @{@.
-}
curlyPairParser :: Parser a -> Parser b -> Parser (a,b)
curlyPairParser pa pb = inCurlyBracesParser (commaSeparatedPairParser pa pb)

{-|'curlyPairRemainderParser' parses two elements between curly braces,
separated by a comma, assumming that the leading @{@ was already consumed.
-}
curlyPairRemainderParser :: Parser a -> Parser (a,a)
curlyPairRemainderParser pa =
    inCurlyBracesRemainderParser (commaSeparatedPairParser pa pa)

{-|'openSquareBracketParser' parses a @[@ character.-}
openSquareBracketParser :: Parser ()
openSquareBracketParser = tokenCharParser '['

{-|'closedSquareBracketParser' parses a @]@ character.-}
closedSquareBracketParser :: Parser ()
closedSquareBracketParser = tokenCharParser ']'

{-|'inSquareBracketsParser' parses an element surrounded by square brackets.

Always starts with @[@.
-}
inSquareBracketsParser :: Parser a -> Parser a
inSquareBracketsParser p =
    openSquareBracketParser *> p <* closedSquareBracketParser

{-|'closedSquareBracketParser' parses a @,@ character.-}
commaParser :: Parser ()
commaParser = tokenCharParser ','

{-|'mlLexemeParser' consumes the provided string, checking that it is not
followed by a character which could be part of an @object-identifier@.
-}
mlLexemeParser :: String -> Parser ()
mlLexemeParser s =
    lexeme (void (Parser.string s <* keywordEndParser))

{-|'keywordEndParser' checks that the next character cannot be part of an
@object-identifier@.
-}
keywordEndParser :: Parser ()
keywordEndParser = do
    mc <- peekChar
    case mc of
        Nothing -> return ()
        Just c -> when (c `CharSet.elem` idCharSet) $
            fail "Expecting keyword to end."

{-|'keywordBasedParsers' consumes one of the strings in the provided pairs,
then parses an element using the corresponding parser. Checks that the consumed
string is not followed by a character which could be part of an
@object-identifier@.

Fails if one of the strings is a prefix of another one.
-}
keywordBasedParsers :: [(String, Parser a)] -> Parser a
keywordBasedParsers = prefixBasedParsers mlLexemeParser

{-|'prefixBasedParsers' consumes one of the strings in the provided pairs,
then parses an element using the corresponding parser.

Fails if one of the strings is a prefix of another one.
-}
prefixBasedParsers ::  (String -> Parser ()) ->[(String, Parser a)] -> Parser a
prefixBasedParsers _ [] = error "Keyword Based Parsers - no parsers"
prefixBasedParsers prefixParser [(k, p)] = prefixParser k *> p
prefixBasedParsers prefixParser stringParsers = do
    c <- peekChar'
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

{-|'metaSortTrie' is a trie containing all the possible metasorts.-}
metaSortTrie :: HashMap Char8.ByteString MetaSortType
metaSortTrie =
    HashMap.fromList $
        map (\s -> (Char8.pack (show s), s)) metaSortsListWithString

{-|'metaSortConverter' converts a string representation of a metasort name
(without the leading '#') to a 'MetaSortType'.
-}
metaSortConverter :: String -> Maybe MetaSortType
-- TODO(virgil): Does the pack call matter for performance? Should we try to
-- improve it?
metaSortConverter identifier = HashMap.lookup (Char8.pack identifier) metaSortTrie
