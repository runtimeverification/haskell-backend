{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

All exported parsers consume the whitespace after the parsed element and expect
no whitespace before.
 -}
module Kore.Parser.Lexer
    (
    -- * Lexemes
      lexeme
    , symbol
    , comma
    , colon
    , skipChar
    , lbrace, rbrace, braces
    , lparen, rparen, parens
    , lbracket, rbracket, brackets
    , space
    , keyword
    , pair, tuple, list
    , parensPair, parensTuple
    , bracesPair
    -- * Primitive parsers
    , parseId
    , parseAnyId, parseSetId, isSymbolId
    , isElementVariableId, isSetVariableId
    , parseSortId
    , parseSymbolId
    , parseModuleName
    , parseStringLiteral
    -- * Error messages
    , unrepresentableCode
    , illegalSurrogate
    ) where

import Prelude.Kore

import qualified Control.Monad as Monad
import qualified Data.Char as Char
import Data.HashSet
    ( HashSet
    )
import qualified Data.HashSet as HashSet
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
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

import Kore.Parser.ParserUtils as ParserUtils
import Kore.Sort
import Kore.Syntax.Definition
import Kore.Syntax.StringLiteral

{-|'lexeme' transforms a raw parser into one that skips the whitespace and any
comments after the parsed element.
-}
lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

{- | Skip whitespace and C-style comments

* @\/\/@ line comment
* @\/*@ block comment (non-nested) @*\/@

See also: 'L.space'

-}
space ::  Parser ()
space = L.space Parser.space1 lineComment blockComment
  where
    lineComment = L.skipLineComment "//"
    blockComment = L.skipBlockComment "/*" "*/"
{-# INLINE space #-}

{- | Parse the character, but skip its result.
 -}
skipChar :: Char -> Parser ()
skipChar = Monad.void . Parser.char

{- | Skip a literal string (symbol) and any trailing whitespace.

@symbol@ does not enforce that there is whitespace after the symbol.

See also: 'L.symbol', 'space'

 -}
symbol :: String -> Parser ()
symbol = Monad.void . L.symbol space

colon :: Parser ()
colon = symbol ":"

lbrace :: Parser ()
lbrace = symbol "{"

rbrace :: Parser ()
rbrace = symbol "}"

braces :: Parser a -> Parser a
braces = Parser.between lbrace rbrace

lparen :: Parser ()
lparen = symbol "("

rparen :: Parser ()
rparen = symbol ")"

parens :: Parser a -> Parser a
parens = Parser.between lparen rparen

tuple :: Parser a -> Parser b -> Parser (a, b)
tuple parseA parseB = do
    a <- parseA
    comma
    b <- parseB
    pure (a, b)

pair :: Parser a -> Parser (a, a)
pair parseItem = tuple parseItem parseItem

list :: Parser a -> Parser [a]
list item = Parser.sepBy item comma

parensPair :: Parser a -> Parser (a, a)
parensPair parseItem = parens (pair parseItem)

parensTuple :: Parser a -> Parser b -> Parser (a, b)
parensTuple parseA parseB = parens (tuple parseA parseB)

bracesPair :: Parser a -> Parser (a, a)
bracesPair parseItem = braces (pair parseItem)

lbracket :: Parser ()
lbracket = symbol "["

rbracket :: Parser ()
rbracket = symbol "]"

brackets :: Parser a -> Parser a
brackets = Parser.between lbracket rbracket

comma :: Parser ()
comma = symbol ","

{- | Parse a literal keyword.

@keyword@ checks that the keyword is not actually part of an identifier and
consumes any trailing whitespace.

See also: 'space'

 -}
keyword :: String -> Parser ()
keyword s = lexeme $ do
    _ <- Parser.chunk s
    -- Check that the next character cannot be part of an @id@, i.e.  check that
    -- we have just parsed a keyword and not the first part of an identifier.
    Parser.notFollowedBy $ Parser.satisfy isIdChar

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
    !pos <- sourcePosToFileLocation <$> getSourcePos
    name <- lexeme stringRawParser
    return Id
        { getId = Text.pack name
        , idLocation = AstLocationFile pos
        }
{-# INLINE stringParserToIdParser #-}

koreKeywordsSet :: HashSet String
koreKeywordsSet = HashSet.fromList keywords
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
    :: (Char -> Bool)  -- ^ contains the characters allowed for @⟨prefix-char⟩@.
    -> (Char -> Bool)  -- ^ contains the characters allowed for @⟨body-char⟩@.
    -> IdKeywordParsing
    -> Parser String
genericIdRawParser isFirstChar isBodyChar idKeywordParsing = do
    c <- Parser.satisfy isFirstChar <?> "first identifier character"
    cs <- Parser.takeWhileP (Just "identifier character") isBodyChar
    let genericId = c : cs
        keywordsForbidden = idKeywordParsing == KeywordsForbidden
        isKeyword = HashSet.member genericId koreKeywordsSet
    when (keywordsForbidden && isKeyword)
        $ fail
            (  "Identifiers should not be keywords: '"
            ++ genericId
            ++ "'."
            )
    return genericId

{- |

@
<id-first-char>
  ::= ['A'..'Z', 'a'..'z']
@

-}
isIdFirstChar :: Char -> Bool
isIdFirstChar c = ('A' <= c && c <= 'Z') || ('a' <= c && c <= 'z')
{-# INLINE isIdFirstChar #-}

{- |

@
<id-other-char>
  ::= ['0'..'9', '\'', '-']
@

-}
isIdOtherChar :: Char -> Bool
isIdOtherChar c = ('0' <= c && c <= '9') || c == '\'' || c == '-'
{-# INLINE isIdOtherChar #-}

{- |

@
<id-char>
  ::= <id-first-char>
    | <id-other-char>
@

-}
isIdChar :: Char -> Bool
isIdChar c = isIdFirstChar c || isIdOtherChar c
{-# INLINE isIdChar #-}

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
parseId :: Parser Id
parseId = stringParserToIdParser (parseIdRaw KeywordsForbidden)

parseIdRaw :: IdKeywordParsing -> Parser String
parseIdRaw = genericIdRawParser isIdFirstChar isIdChar

{- | Parse a module name.

@
<module-name-id> ::= <id>
@
-}
parseModuleName :: Parser ModuleName
parseModuleName = lexeme moduleNameRawParser

moduleNameRawParser :: Parser ModuleName
moduleNameRawParser =
  ModuleName . Text.pack <$> parseIdRaw KeywordsForbidden

{- | Parses a 'Sort' 'Id'

@
<sort-id> ::= <id>
@
-}
parseSortId :: Parser Id
parseSortId = parseId <?> "sort identifier"

parseAnyId :: Parser Id
parseAnyId = (parseSpecialId <|> parseSetId <|> parseId) <?> "identifier"

isSymbolId :: Id -> Bool
isSymbolId Id { getId } =
    isIdFirstChar c || c == '\\'
  where
    c = Text.head getId

isElementVariableId :: Id -> Bool
isElementVariableId Id { getId } =
    isIdFirstChar (Text.head getId)

isSetVariableId :: Id -> Bool
isSetVariableId Id { getId } = Text.head getId == '@'

parseSpecialId :: Parser Id
parseSpecialId =
    stringParserToIdParser parseSpecialIdString
  where
    parseSpecialIdString =
        (:) <$> Parser.char '\\' <*> parseIdRaw KeywordsPermitted

parseSetId :: Parser Id
parseSetId =
    stringParserToIdParser parseSetIdString
  where
    parseSetIdString =
        (:) <$> Parser.char '@' <*> parseIdRaw KeywordsPermitted

{- | Parses a 'Symbol' 'Id'

@
<symbol-id> ::= ['\']?<id>
@
-}
parseSymbolId :: Parser Id
parseSymbolId =
    stringParserToIdParser symbolIdRawParser <?> "symbol or alias identifier"

symbolIdRawParser :: Parser String
symbolIdRawParser = do
    c <- peekChar'
    if c == '\\'
    then do
        skipChar '\\'
        (c :) <$> parseIdRaw KeywordsPermitted
    else parseIdRaw KeywordsForbidden

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
parseStringLiteral :: Parser StringLiteral
parseStringLiteral = lexeme stringLiteralRawParser

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
    let i = foldl' (\r h -> 0x10 * r + Char.digitToInt h) 0 hs
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
