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

All exported parsers consume the whitespace after the parsed element and expect
no whitespace before.
-}
module Kore.Parser.Lexeme
    (
    -- * Parsers
      colonParser
    , commaParser
    , curlyPairParser
    , curlyPairRemainderParser
    , idParser
    , elementVariableIdParser
    , setVariableIdParser
    , sortIdParser
    , symbolIdParser
    , idFirstChars
    , idOtherChars
    , openCurlyBraceParser
    , closedCurlyBraceParser
    , inCurlyBracesParser
    , inCurlyBracesRemainderParser
    , inParenthesesParser
    , inSquareBracketsParser
    , keywordBasedParsers
    , mlLexemeParser
    , moduleNameIdParser
    , parenPairParser
    , skipChar
    , skipWhitespace
    , stringLiteralParser
    -- * Error messages
    , unrepresentableCode
    , illegalSurrogate
    ) where

import qualified Control.Monad as Monad
import qualified Data.ByteString.Char8 as Char8
import qualified Data.Char as Char
import qualified Data.Foldable as Foldable
import Data.HashSet
    ( HashSet
    )
import qualified Data.HashSet as HashSet
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Text as Text
import Text.Megaparsec
    ( SourcePos (..)
    , anySingle
    , getSourcePos
    , unPos
    , (<?>)
    )
import qualified Text.Megaparsec as Parser
import qualified Text.Megaparsec.Char as Parser
import qualified Text.Megaparsec.Char.Lexer as L

import qualified Kore.Parser.CharDict as CharDict
import Kore.Parser.CharSet as CharSet
import Kore.Parser.ParserUtils as ParserUtils
import Kore.Sort
import Kore.Syntax.Definition
import Kore.Syntax.StringLiteral

{-|'lexeme' transforms a raw parser into one that skips the whitespace and any
comments after the parsed element.
-}
lexeme :: Parser a -> Parser a
lexeme = L.lexeme skipWhitespace

{-|'skipWhitespace' skips whitespace and C-style comments:

- @//@ line comment
- @/*@ block comment (non-nested) @*/@
-}
skipWhitespace ::  Parser ()
skipWhitespace =
    L.space Parser.space1 lineComment blockComment
  where
    lineComment = L.skipLineComment "//"
    blockComment = L.skipBlockComment "/*" "*/"

{- | Parse the character, but skip its result.
 -}
skipChar :: Char -> Parser ()
skipChar = Monad.void . Parser.char

{- | Parse the string, but skip its result.
 -}
skipString :: String -> Parser ()
skipString = Monad.void . Parser.string

{-|'tokenCharParser' parses a character, skipping any whitespace after.

Note that it does not enforce the existence of whitespace after the character.
-}
tokenCharParser :: Char -> Parser ()
tokenCharParser c = Monad.void $ L.symbol skipWhitespace [c]

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
    lexeme (skipString s <* keywordEndParser)

{-|'keywordEndParser' checks that the next character cannot be part of an
@object-identifier@.
-}
keywordEndParser :: Parser ()
keywordEndParser = do
    mc <- peekChar
    case mc of
        Just c
          | CharSet.elem c idCharSet ->
            fail "Expecting keyword to end."
        _ -> return ()

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

{- Takes a parser for the string of the identifier
   and returns an 'Id' annotated with position.
-}
stringParserToIdParser :: Parser String -> Parser Id
stringParserToIdParser stringRawParser = do
    pos <- sourcePosToFileLocation <$> getSourcePos
    name <- lexeme stringRawParser
    return Id
        { getId = Text.pack name
        , idLocation = AstLocationFile pos
        }

koreKeywordsSet :: HashSet Char8.ByteString
koreKeywordsSet = HashSet.fromList (Char8.pack <$> keywords)
  where
    keywords =
        [ "module"
        , "endmodule"
        , "import"
        , "sort"
        , "hooked-sort"
        , "symbol"
        , "hooked-symbol"
        , "axiom"
        , "claim"
        , "alias"
        , "where"
        ]

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
    Monad.when
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

idFirstChars :: [Char]
idFirstChars = ['A'..'Z'] ++ ['a'..'z']

idFirstCharSet :: CharSet
idFirstCharSet = CharSet.makeCharSet idFirstChars

idOtherChars :: [Char]
idOtherChars = ['0'..'9'] ++ "'-"

idCharSet :: CharSet
idCharSet =
    CharSet.join idFirstCharSet (CharSet.makeCharSet idOtherChars)

{- | Parses an identifier.

@
<id-first-char>
  ::= ['A'..'Z', 'a'..'z']
<id-other-char>
  ::= ['0'..'9', '\'', '-']
<id-char>
  ::= <id-first-char>
    | <id-other-char>
<id>
  ::= <id-first-char> <id-char>*
@

An identifier cannot be a keyword.
-}
idParser :: Parser Id
idParser = stringParserToIdParser (idRawParser KeywordsForbidden)

idRawParser :: IdKeywordParsing -> Parser String
idRawParser =
    genericIdRawParser idFirstCharSet idCharSet

{- | Parses a module name.

@
<module-name-id> ::= <id>
@
-}
moduleNameIdParser :: Parser ModuleName
moduleNameIdParser = lexeme moduleNameRawParser

moduleNameRawParser :: Parser ModuleName
moduleNameRawParser =
  ModuleName . Text.pack <$> idRawParser KeywordsForbidden

{- | Parses a 'Sort' 'Id'

@
<sort-id> ::= <id>
@
-}
sortIdParser :: Parser Id
sortIdParser = idParser

{- | Parses a 'Symbol' 'Id'

@
<symbol-id> ::= ['\']?<id>
@
-}
symbolIdParser :: Parser Id
symbolIdParser = stringParserToIdParser symbolIdRawParser

symbolIdRawParser :: Parser String
symbolIdRawParser = do
    c <- peekChar'
    if c == '\\'
    then do
        skipChar '\\'
        (c :) <$> idRawParser KeywordsPermitted
    else idRawParser KeywordsForbidden

{-|Parses a @set-variable-id@, which always starts with @\@@.

@
<set-variable-id> ::= ['@'] <id>
@
-}
setVariableIdParser :: Parser Id
setVariableIdParser = stringParserToIdParser setVariableIdRawParser

setVariableIdRawParser :: Parser String
setVariableIdRawParser = do
    start <- Parser.char '@'
    end <- idRawParser KeywordsPermitted
    return (start:end)

{-| Parses an @element-variable-id@

@
<element-variable-id> ::= <id>
@
-}
elementVariableIdParser :: Parser Id
elementVariableIdParser = idParser

{- | Parses a C-style string literal, unescaping it.

@
<string-literal>
  ::= ['"'] <char>* ['"']

<char>
  ::= <escape-char>
    | <ascii-char>
    | <printable-char>

<ascii-char>
  ::= first 128 ASCII characters, except '"'
<printable-char>
  ::= printable according to the C++ iswprint function, except '"'

<escape-char>
  ::= ['\'] <escaped-char>

<escaped-char>
  ::= ['"', '\', 'f', 'n', 'r', 't']
    | ['x'] <hex-digit2>
    | ['u'] <hex-digit4>
    | ['U'] <hex-digit8>

<hex-digit>
  ::= ['0'..'9', 'A'..'F', 'a'..'f']
<hex-digit2>
  ::= <hex-digit> <hex-digit>
<hex-digit4>
  ::= <hex-digit2> <hex-digit2>
<hex-digit8>
  ::= <hex-digit4> <hex-digit4>
@
-}
stringLiteralParser :: Parser StringLiteral
stringLiteralParser = lexeme stringLiteralRawParser

stringLiteralRawParser :: Parser StringLiteral
stringLiteralRawParser = do
    skipChar '"'
    StringLiteral . Text.pack <$> Parser.manyTill charParser (skipChar '"')

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

{- Parse a single character.

The character may be escaped, in which case the unescaped character is
returned. @charParser@ is used for parsing string and character literals.

 -}
charParser :: Parser Char
charParser = do
    c <- peekChar'
    if c == '\\'
        then escapeParser
        else asciiPrintCharParser

{- | Parse an escape sequence.
 -}
escapeParser :: Parser Char
escapeParser =
    Parser.label "escape sequence" $ do
        skipChar '\\'
        c <- anySingle
        fromMaybe
            (Parser.empty <?> "escape sequence")
            (Map.lookup c escapeParsers)
{-# INLINE escapeParser #-}

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
    hs <- Monad.replicateM n hexDigitParser
    let i = Foldable.foldl' (\r h -> 0x10 * r + Char.digitToInt h) 0 hs
    Monad.when (i > Char.ord (maxBound :: Char)) $ fail (unrepresentableCode hs)
    let c = Char.chr i
    Monad.when (isSurrogate c) $ fail (illegalSurrogate hs)
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

