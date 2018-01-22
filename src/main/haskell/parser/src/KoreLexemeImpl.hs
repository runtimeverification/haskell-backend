{-|
Module      : KoreLexemeImpl
Description : Lexical unit definitions for Kore and simple ways of composing
              parsers. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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

4. The "Raw" parsers do not consume any whitespace.
-}
module KoreLexemeImpl where

import qualified CharDict
import           CharSet
import           CString
import           KoreAST
import           ParserUtils

import           Control.Monad                    (void, when)
import qualified Data.Attoparsec.ByteString       as BParser (runScanner)
import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser ( char
                                                            , peekChar
                                                            , peekChar'
                                                            , scan
                                                            , skipSpace
                                                            , string
                                                            , takeWhile
                                                            )
import qualified Data.ByteString.Char8            as Char8
import           Data.Char                        (isHexDigit, isOctDigit)
import           Data.Maybe                       (isJust)
import qualified Data.Trie                        as Trie

{-|'idParser' parses either an @object-identifier@, or a @meta-identifier@.

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
idParser :: IsMeta a
         => a  -- ^ Distinguishes between the meta and non-meta elements.
         -> Parser (Id a)
idParser x = Id <$> lexeme (idRawParser x)

{-|'stringLiteralParser' parses a C-style string literal, unescaping it.

Always starts with @"@.
-}
stringLiteralParser :: Parser StringLiteral
stringLiteralParser = lexeme stringLiteralRawParser

{-|'moduleNameParser' parses a module name.-}
moduleNameParser :: Parser ModuleName
moduleNameParser = lexeme moduleNameRawParser

data CommentScannerState = COMMENT | STAR | END

{-|'skipMultiLineCommentReminder' skips a C-style multiline comment after the
leading @/*@ was already consumed.
-}
skipMultiLineCommentReminder :: Parser ()
skipMultiLineCommentReminder = do
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

{-|'skipSingleLineCommentReminder' skips a C-style single line comment after the
leading @//@ was already consumed.
-}
skipSingleLineCommentReminder :: Parser ()
skipSingleLineCommentReminder =
    void (Parser.scan COMMENT delta)
  where
    delta END _  = Nothing
    delta _ '\n' = Just END
    delta _ _    = Just COMMENT


spaceChars :: [Char]
spaceChars = [' ', '\t', '\n', '\v', '\f', '\r']

{-|'skipWhitespace' skips whitespace-like content until the first non-whitespace
character or the end of the input.
-}
skipWhitespace :: Parser ()
skipWhitespace =
    prefixBasedParsersWithDefault
        skipString
        (return ())
        (
            [ ("/*", skipMultiLineCommentReminder *> skipWhitespace)
            , ("//", skipSingleLineCommentReminder *> skipWhitespace)
            ]
            ++
            map (\c -> ([c], Parser.skipSpace *> skipWhitespace)) spaceChars
        )

{-|'lexeme' transforms a raw parser into one that skips the whitespace
after the parsed element.
-}
lexeme :: Parser a -> Parser a
lexeme p = p <* skipWhitespace

koreKeywordsSet :: Trie.Trie ()
koreKeywordsSet = Trie.fromList $ map (\s -> (Char8.pack s, ()))
    ["module", "endmodule", "sort", "symbol", "alias", "axiom"]

{-|'genericIdRawParser' parses for tokens that can be represented as
@⟨prefix-char⟩ ⟨body-char⟩*@. Does not consume whitespace.
-}
genericIdRawParser
    :: CharSet  -- ^ contains the characters allowed for @⟨prefix-char⟩@.
    -> CharSet  -- ^ contains the characters allowed for @⟨body-char⟩@.
    -> Parser String
genericIdRawParser firstCharSet bodyCharSet = do
    c <- Parser.peekChar'
    idChar <- if not (c `CharSet.elem` firstCharSet)
        then fail ("genericIdRawParser: Invalid first character '" ++ c : "'.")
        else Parser.takeWhile (`CharSet.elem` bodyCharSet)
    let identifier = Char8.unpack idChar
    when (isJust $ Trie.lookup idChar koreKeywordsSet)
        (fail ("Identifiers should not be keywords: '" ++ identifier ++ "'."))
    return identifier

moduleNameFirstCharSet :: CharSet
moduleNameFirstCharSet = idFirstCharSet

moduleNameCharSet :: CharSet
moduleNameCharSet = idCharSet


{-|'moduleNameRawParser' parses a @module-name@. Does not consume whitespace.-}
moduleNameRawParser :: Parser ModuleName
moduleNameRawParser =
  ModuleName <$> genericIdRawParser moduleNameFirstCharSet moduleNameCharSet

idFirstCharSet :: CharSet
idFirstCharSet = CharSet.makeCharSet (['A'..'Z'] ++ ['a'..'z'])

idCharSet :: CharSet
idCharSet =
    CharSet.join idFirstCharSet (CharSet.makeCharSet (['0'..'9'] ++ "'-"))

{-|'objectIdRawParser' extracts the string representing an @object-identifier@.
Does not consume whitespace.
-}
objectIdRawParser :: Parser String
objectIdRawParser = genericIdRawParser idFirstCharSet idCharSet

{-|'metaIdRawParser' extracts the string representing a @meta-identifier@.
Does not consume whitespace.

Always starts with @#@
-}
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

{-|'idParser' parses either an @object-identifier@, or a @meta-identifier@.
Does not consume whitespace.

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
idRawParser :: (IsMeta a)
            => a  -- ^ Distinguishes between the meta and non-meta elements.
            -> Parser String
idRawParser x = case metaType x of
    ObjectType -> objectIdRawParser
    MetaType   -> metaIdRawParser

data StringScannerState = STRING | ESCAPE | HEX StringScannerState

{-|'stringLiteralRawParser' parses a C-style string literal, unescaping it.
Does not consume whitespace.
-}
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

{-|'tokenCharParser' parses a character, skipping any whitespace after.

Note that it does not enforce the existence of whitespace after the character.
-}
tokenCharParser :: Char -> Parser ()
tokenCharParser = skipCharParser skipWhitespace

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

{-|'skipString' consumes the provided string.-}
skipString :: String -> Parser ()
skipString = void . Parser.string . Char8.pack

{-|'mlLexemeParser' consumes the provided string, checking that it is not
followed by a character which could be part of an @object-identifier@.
-}
mlLexemeParser :: String -> Parser ()
mlLexemeParser s =
    lexeme (void (Parser.string (Char8.pack s) <* keywordEndParser))

{-|'keywordEndParser' checks that the next character cannot be part of an
@object-identifier@.
-}
keywordEndParser :: Parser ()
keywordEndParser = do
    mc <- Parser.peekChar
    case mc of
        Nothing -> return ()
        Just c -> if c `CharSet.elem` idCharSet
            then fail "Expecting keyword to end."
            else return ()

{-|'keywordBasedParsers' consumes one of the strings in the provided pairs,
then parses an element using the corresponding parser. Checks that the consumed
string is not followed by a character which could be part of an
@object-identifier@.

Fails if one of the strings is a prefix of another one.
-}
keywordBasedParsers :: [(String, Parser a)] -> Parser a
keywordBasedParsers stringParsers =
    prefixBasedParsers mlLexemeParser stringParsers

{-|'prefixBasedParsers' consumes one of the strings in the provided pairs,
then parses an element using the corresponding parser.

Fails if one of the strings is a prefix of another one.
-}
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

{-|'prefixBasedParsersWithDefault' consumes one of the strings in the provided
pairs, then parses an element using the corresponding parser. If the first
input character does not match any string prefix, it uses the default parser.

Fails if one of the strings is a prefix of another one.
-}
prefixBasedParsersWithDefault
    :: (String -> Parser ())  -- ^ Parser for the prefix strings.
    -> Parser a  -- ^ Element parser.
    -> [(String, Parser a)] -- ^ (prefix, remainder parser) pairs.
    -> Parser a
prefixBasedParsersWithDefault _ _ [] =
    error "Keyword Based Parsers With Default - no parsers"
prefixBasedParsersWithDefault prefixParser defaultParser stringParsers = do
    mc <- Parser.peekChar
    case mc of
        Nothing -> defaultParser
        -- TODO(virgil): Should this lookup be optimized?
        Just c -> if any ((==c).head.fst) stringParsers
            then prefixBasedParsers prefixParser stringParsers
            else defaultParser

{-|'metaSortTrie' is a trie containing all the possible metasorts.-}
metaSortTrie :: Trie.Trie MetaSortType
metaSortTrie = Trie.fromList $ map (\s -> (Char8.pack $ show s, s))
    [ CharSort, CharListSort, PatternSort, PatternListSort, SortSort
    , SortListSort, StringSort, SymbolSort, SymbolListSort
    , VariableSort, VariableListSort
    ]

{-|'metaSortConverter' converts a string representation of a metasort name
(without the leading '#') to a 'MetaSortType'.
-}
metaSortConverter :: String -> Maybe MetaSortType
-- TODO(virgil): Does the pack call matter for performance? Should we try to
-- improve it?
metaSortConverter identifier = Trie.lookup (Char8.pack identifier) metaSortTrie
