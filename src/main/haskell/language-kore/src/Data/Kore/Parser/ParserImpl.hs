{-|
Module      : Data.Kore.Parser.ParserImpl
Description : Parser definition for Kore. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Parser definition for Kore. Meant for internal use only.

Conventions used:

1. In various cases we distinguish between @object-@ and @meta-@ versions of an
   element. For this we parametrize the element's type with an @a@ and we
   provide an element of type @a@ to the parser, usually called @x@.

2. The meta versions are identified by the presence of @#@ characters, usually
   found at the start of the element. However, when they are found inside,
   we may split the parser in two pieces, one that parses everything until the
   first element that may start with @#@ and identifies the value of @x@ and
   another one that receives 'x' and parses the reminder.

3. Whenever we have both an element which can be meta or object and
   an element which is the union of the two, the union is called 'Unified*'.
   As an example, if we have @⟨object-variable⟩@, @⟨meta-variable⟩@ and
   @⟨variable⟩ ::= ⟨object-variable⟩ | ⟨meta-variable⟩@, then we'll represent
   the fist two by "Variable a" and the latter by "UnifiedVariable".

3. Parsers called 'Raw' receive a constructor that constructs the element.

4. Parsers called 'Reminder' receive an element's parsed prefix and an element
   constructor, parse whatever is left of the element and construct it.

5. All parsers consume the whitespace after the parsed element and expect no
   whitespace before.
-}
module Data.Kore.Parser.ParserImpl where

import           Data.Kore.AST
import           Data.Kore.Parser.Lexeme
import qualified Data.Kore.Parser.ParserUtils     as ParserUtils
import           Data.Kore.Unparser.Unparse

import           Control.Arrow                    ((&&&))
import           Control.Monad                    (unless, void, when)

import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser (char, peekChar,
                                                             peekChar')
import           Data.Attoparsec.Combinator       (many1)
import           Data.Maybe                       (isJust)

{-|'sortVariableParser' parses either an @object-sort-variable@, or a
@meta-sort-variable@.

BNF definition:

@
⟨object-sort-variable⟩ ::= ⟨object-identifier⟩
⟨meta-sort-variable⟩ ::= ⟨meta-identifier⟩
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
sortVariableParser
    :: IsMeta a
    => a        -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (SortVariable a)
sortVariableParser x = SortVariable <$> idParser x

{-|'inCurlyBracesSortVariableListParser' parses a comma delimited
@object-sort-variable-list@ or a @meta-sort-variable-list@.

Example BNF definition for @object-sort-variable-list@:

@
⟨object-sort-variable-list⟩ ::=
    | ε
    | ⟨object-sort-variable⟩
    | ⟨object-sort-variable⟩ ‘,’ ⟨object-sort-variable-list⟩
@

Example BNF definition fragment for what we're parsing here:

@
⟨...⟩ ::= ... ‘{’ ⟨object-sort-variable-list⟩ ‘}’ ...
@

Always starts with @{@,
-}
inCurlyBracesSortVariableListParser
    :: IsMeta a
    => a        -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser [SortVariable a]
inCurlyBracesSortVariableListParser x =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '{' '}' ','
        (sortVariableParser x)

{-|'unifiedSortVariableParser' parses a sort variable.-}
unifiedSortVariableParser :: Parser UnifiedSortVariable
unifiedSortVariableParser = do
    c <- Parser.peekChar'
    if c == '#'
        then MetaSortVariable <$> sortVariableParser Meta
        else ObjectSortVariable <$> sortVariableParser Object

{-|'inCurlyBracesUnifiedSortVariableListParser' parses a delimited
@sort-variable-list@.

BNF definition for @sort-variable-list@:

@
⟨sort-variable-list⟩ ::=
    | ε
    | ⟨object-sort-variable⟩
    | ⟨meta-sort-variable⟩
    | ⟨object-sort-variable⟩ ‘,’ ⟨sort-variable-list⟩
    | ⟨meta-sort-variable⟩ ‘,’ ⟨sort-variable-list⟩
@

BNF definition fragment for what we're parsing here:

@
⟨...⟩ ::= ... ‘{’ ⟨sort-variable-list⟩ ‘}’ ...
@

Always starts with @{@,
-}
inCurlyBracesUnifiedSortVariableListParser :: Parser [UnifiedSortVariable]
inCurlyBracesUnifiedSortVariableListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '{' '}' ','
        unifiedSortVariableParser

{-|'sortParser' parses either an @object-sort@, or a @meta-sort@.

BNF definition:

@
⟨object-sort⟩ ::=
    | ⟨object-sort-variable⟩
    | ⟨object-sort-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨meta-sort⟩ ::= ⟨meta-sort-variable⟩ | ⟨meta-sort-constructor⟩ ‘{’ ‘}’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
sortParser
    :: IsMeta a
    => a        -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (Sort a)
sortParser x = do
    identifier <- idParser x
    c <- Parser.peekChar
    case c of
        Just '{' -> actualSortParser identifier
        _        -> return (SortVariableSort $ SortVariable identifier)
  where
    actualSortParser identifier = do
        sorts <- inCurlyBracesSortListParser x
        when (koreLevel x == MetaLevel) (validateMetaSort identifier sorts)
        return $ SortActualSort SortActual
            { sortActualName = stringNameNormalizer identifier
            , sortActualSorts = sorts
            }
    stringNameNormalizer identifier@(Id i) =
        if (koreLevel x == MetaLevel) && (i == show StringSort)
            then Id (show CharListSort)
            else identifier

{-|'validateMetaSort' checks that a @meta-sort@ is well-formed.

Relevant BNF definitions:

@
⟨meta-sort⟩ ::= ⟨meta-sort-variable⟩ | ⟨meta-sort-constructor⟩ ‘{’ ‘}’
⟨meta-sort-constructor⟩ ::=
    | ‘#Char’       | ‘#CharList’   | ‘#String’
    | ‘#Sort’       | ‘#SortList’   | ‘#Symbol’
    | ‘#SymbolList’ | ‘#Variable’   | ‘#VariableList’
    | ‘#Pattern’    | ‘#PatternList’
@
-}
validateMetaSort
    :: Show a
    => Id a     -- ^ The sort name
    -> [Sort a] -- ^ The sort arguments
    -> Parser ()
validateMetaSort identifier [] =
    unless (isJust (metaSortConverter metaId))
        (fail ("metaSortConverter: Invalid constructor: '" ++ metaId ++ "'."))
  where
    metaId = getId identifier
validateMetaSort _ _ = fail "metaSortConverter: Non empty parameter sorts."

{-|'inCurlyBracesSortListParser' parses either an @object-sort-list@
or a @meta-sort-list@, delimited by curly braces and separated by commas.

BNF definitions:

@
⟨object-sort-list⟩ ::= ε | ⟨object-sort⟩ | ⟨object-sort⟩ ‘,’ ⟨object-sort-list⟩
⟨meta-sort-list⟩ ::= ε | ⟨meta-sort⟩ | ⟨meta-sort⟩ ‘,’ ⟨meta-sort-list⟩
@

BNF definition fragment for what we're parsing here:

@
⟨...⟩ ::= ... ‘{’ ⟨object-sort-list⟩ ‘}’ ...
⟨...⟩ ::= ... ‘{’ ⟨meta-sort-list⟩ ‘}’ ...
@

Always starts with @{@,
-}
inCurlyBracesSortListParser
    :: IsMeta a
    => a        -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser [Sort a]
inCurlyBracesSortListParser x =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '{' '}' ','
        (sortParser x)

{-|'inParenthesesSortListParser' is similar to
'inCurlyBracesSortListParser', except that it uses parentheses
instead of curly braces.
-}
inParenthesesSortListParser :: IsMeta a => a -> Parser [Sort a]
inParenthesesSortListParser x =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '(' ')' ','
        (sortParser x)

{-|'symbolOrAliasDeclarationRawParser' parses a head and constructs it using the provided
constructor.

BNF definitions:

@
⟨object-head⟩ ::= ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨meta-head⟩ ::= ⟨meta-head-constructor⟩ ‘{’ ⟨meta-sort-list⟩ ‘}’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
symbolOrAliasDeclarationRawParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Id a -> [SortVariable a] -> m a)  -- ^ Element constructor.
    -> Parser (m a)
symbolOrAliasDeclarationRawParser x constructor = do
    headConstructor <- idParser x
    symbolOrAliasDeclarationRemainderRawParser x (constructor headConstructor)

{-|'symbolOrAliasDeclarationRemainderRawParser' parses the sort list that occurs
in heads and constructs the head using the provided constructor.

BNF fragments:

@
... ::= ... ‘{’ ⟨object-sort-variable-list⟩ ‘}’ ...
... ::= ... ‘{’ head-sort-variable-list⟩ ‘}’ ...
@

Always starts with @{@.
-}
symbolOrAliasDeclarationRemainderRawParser
    :: IsMeta a
    => a   -- ^ Distinguishes between the meta and non-meta elements.
    -> ([SortVariable a] -> m a)  -- ^ Element constructor.
    -> Parser (m a)
symbolOrAliasDeclarationRemainderRawParser x constructor =
    constructor <$> inCurlyBracesSortVariableListParser x

{-|'aliasParser' parses either an @object-head@ or a @meta-head@ and interprets
it as an alias head.

BNF definitions:

@
⟨object-head⟩ ::= ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨meta-head⟩ ::= ⟨meta-head-constructor⟩ ‘{’ ⟨meta-sort-list⟩ ‘}’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
aliasParser
    :: IsMeta a
    => a        -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (Alias a)
aliasParser x = symbolOrAliasDeclarationRawParser x Alias


{-|'symbolParser' is the same as 'aliasParser', but it interprets the head
as a symbol one.
-}
symbolParser :: IsMeta a => a -> Parser (Symbol a)
symbolParser x = symbolOrAliasDeclarationRawParser x Symbol

{-|'unaryOperatorRemainderParser' parses the part after an unary operator's
name and the first open curly brace and constructs it using the provided
constructor.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
unaryOperatorRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort a -> UnifiedPattern -> m a UnifiedPattern)
    -- ^ Element constructor.
    -> Parser (m a UnifiedPattern)
unaryOperatorRemainderParser x constructor =
    pure constructor
        <*> inCurlyBracesRemainderParser (sortParser x)
        <*> inParenthesesParser patternParser

{-|'binaryOperatorRemainderParser' parses the part after a binary operator's
name and the first open curly brace and constructs it using the provided
constructor.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
binaryOperatorRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort a -> UnifiedPattern -> UnifiedPattern -> m a UnifiedPattern)
    -- ^ Element constructor.
    -> Parser (m a UnifiedPattern)
binaryOperatorRemainderParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    (pattern1, pattern2) <-
        parenPairParser patternParser patternParser
    return (constructor sort pattern1 pattern2)

{-|'existsForallRemainderParser' parses the part after an exists or forall
operator's name and the first open curly brace and constructs it using the
provided constructor.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨object-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘}’ ‘(’ ⟨meta-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
existsForallRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort a -> Variable a -> UnifiedPattern
        -> m a Variable UnifiedPattern)
    -- ^ Element constructor.
    -> Parser (m a Variable UnifiedPattern)
existsForallRemainderParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    (variable, qPattern) <- parenPairParser (variableParser x) patternParser
    return (constructor sort variable qPattern)

{-|'ceilFloorRemainderParser' parses the part after a ceil or floor
operator's name and the first open curly brace and constructs it using the
provided constructor.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
ceilFloorRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort a -> Sort a -> UnifiedPattern -> m a UnifiedPattern)
    -- ^ Element constructor.
    -> Parser (m a UnifiedPattern)
ceilFloorRemainderParser x constructor = do
    (sort1, sort2) <- curlyPairRemainderParser (sortParser x)
    cfPattern <- inParenthesesParser patternParser
    return (constructor sort1 sort2 cfPattern)

{-|'inRemainderParser' parses the part after a in
operator's name and the first open curly brace and constructs it.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
inRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (In a UnifiedPattern)
inRemainderParser x = do
    (sort1, sort2) <- curlyPairRemainderParser (sortParser x)
    (cdPattern, cgPattern) <-
        parenPairParser patternParser patternParser
    return In
           { inOperandSort = sort1
           , inResultSort = sort2
           , inContainedChild = cdPattern
           , inContainingChild = cgPattern
           }

{-|'equalsLikeRemainderParser' parses the part after an equals
operator's name and the first open curly brace and constructs it using the
provided constructor.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
equalsLikeRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort a -> Sort a -> UnifiedPattern -> UnifiedPattern -> m a UnifiedPattern)
    -- ^ Element constructor.
    -> Parser (m a UnifiedPattern)
equalsLikeRemainderParser x constructor = do
    (sort1, sort2) <- curlyPairRemainderParser (sortParser x)
    (pattern1, pattern2) <-
        parenPairParser patternParser patternParser
    return (constructor sort1 sort2 pattern1 pattern2)

{-|'topBottomRemainderParser' parses the part after a top or bottom
operator's name and the first open curly brace and constructs it using the
provided constructor.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ‘)’
... ::= ... ⟨meta-sort⟩ ‘}’ ‘(’ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
topBottomRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort a -> m a p)  -- ^ Element constructor.
    -> Parser (m a p)
topBottomRemainderParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    inParenthesesParser (return ())
    return (constructor sort)

{-|'symbolOrAliasPatternRemainderParser' parses the part after a the first
identifier in an application pattern and constructs it.

BNF fragments:

@
⟨object-pattern⟩ = ⟨object-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
⟨object-head⟩ ::= ... ‘{’ ⟨object-sort-list⟩ ‘}’

⟨meta-pattern⟩ = ⟨meta-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
⟨meta-head⟩ ::= ... ‘{’ ⟨meta-sort-list⟩ ‘}’
@

Always starts with @{@.
-}
symbolOrAliasPatternRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> Id a  -- ^ The already parsed prefix.
    -> Parser (Pattern a Variable UnifiedPattern)
symbolOrAliasPatternRemainderParser x identifier = ApplicationPattern <$>
    ( pure Application
        <*> (SymbolOrAlias identifier <$> inCurlyBracesSortListParser x)
        <*> inParenthesesPatternListParser
    )

{-|'variableRemainderParser' parses the part after a variable's name and
constructs it.

BNF fragments:

@
⟨object-variable⟩ ::= ... ‘:’ ⟨object-sort⟩
@

Always starts with @:@.
-}
variableRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> Id a  -- ^ The already parsed prefix.
    -> Parser (Variable a)
variableRemainderParser x identifier = do
    colonParser
    sort <- sortParser x
    return Variable
        { variableName = identifier
        , variableSort = sort
        }

{-|'variableParser' parses either an @object-variable@, or a @meta-variable@.

BNF definitions:

@
⟨object-variable⟩ ::= ⟨object-identifier⟩ ‘:’ ⟨object-sort⟩
⟨meta-variable⟩ ::= ⟨meta-identifier⟩ ‘:’ ⟨meta-sort⟩
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
variableParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (Variable a)
variableParser x = idParser x >>= variableRemainderParser x

{-|'unifiedVariableParser' parses a @variable@.

BNF definitions:

@
⟨variable⟩ ::= ⟨object-variable⟩ | ⟨meta-variable⟩
@
-}
unifiedVariableParser :: Parser (UnifiedVariable Variable)
unifiedVariableParser = do
    c <- Parser.peekChar'
    if c == '#'
        then MetaVariable <$> variableParser Meta
        else ObjectVariable <$> variableParser Object

{-|'variableOrTermPatternParser' parses an (object or meta) (variable pattern or
application pattern).

BNF definitions:

@
⟨object-pattern⟩ ::=
    | ⟨object-variable⟩
    | ⟨object-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
⟨object-variable⟩ ::= ⟨object-identifier⟩ ‘:’ ⟨object-sort⟩
⟨object-head⟩ ::= ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨object-head-constructor⟩ ::= ⟨object-identifier⟩

⟨meta-pattern⟩ ::=
    | ⟨meta-variable⟩
    | ⟨meta-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
⟨meta-variable⟩ ::= ⟨meta-identifier⟩ ‘:’ ⟨meta-sort⟩
⟨meta-head⟩ ::= ⟨meta-head-constructor⟩ ‘{’ ⟨meta-sort-list⟩ ‘}’
⟨meta-head-constructor⟩ ::= ⟨meta-identifier⟩
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
variableOrTermPatternParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (Pattern a Variable UnifiedPattern)
variableOrTermPatternParser x = do
    identifier <- idParser x
    c <- Parser.peekChar'
    if c == ':'
        then VariablePattern <$> variableRemainderParser x identifier
        else symbolOrAliasPatternRemainderParser x identifier

{-|'unifiedVariableOrTermPatternParser' parses a variable pattern or an
application one.

BNF definitions:

@
⟨object-pattern⟩ ::=
    | ⟨object-variable⟩
    | ⟨object-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
⟨meta-pattern⟩ ::=
    | ⟨meta-variable⟩
    | ⟨meta-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
@
-}
unifiedVariableOrTermPatternParser :: Parser UnifiedPattern
unifiedVariableOrTermPatternParser = do
    c <- Parser.peekChar'
    if c == '#'
        then MetaPattern <$> variableOrTermPatternParser Meta
        else ObjectPattern <$> variableOrTermPatternParser Object

{-|'mlConstructorParser' parses a pattern starting with @\@.

BNF definitions:

@
⟨object-pattern⟩ ::=
    | ‘\and’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\not’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\or’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\implies’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\iff’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\forall’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨object-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\exists’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨object-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\ceil’ ‘{’ ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\floor’ ‘{’ ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\equals’ ‘{’ ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\in’ ‘{’ ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ pattern ‘,’ ⟨pattern⟩ ‘)’
    | ‘\next’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\rewrites’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\top’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ‘)’
    | ‘\bottom’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ‘)’

⟨meta-pattern⟩ ::=
    | ‘\and’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\not’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\or’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\implies’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\iff’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\forall’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨meta-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\exists’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨meta-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\ceil’ ‘{’ ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\floor’ ‘{’ ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\equals’ ‘{’ ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\in’ ‘{’ ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ pattern ‘,’ ⟨pattern⟩ ‘)’
    | ‘\top’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ‘)’
    | ‘\bottom’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ‘)’
@

Always starts with @\@.
-}
mlConstructorParser :: Parser UnifiedPattern
mlConstructorParser = do
    void (Parser.char '\\')
    mlPatternParser
  where
    mlPatternParser = keywordBasedParsers
        (map (patternString &&& mlConstructorRemainderParser) allPatternTypes)
    mlConstructorRemainderParser patternType = do
        openCurlyBraceParser
        c <- Parser.peekChar'
        if c == '#'
            then MetaPattern <$>
                mlConstructorRemainderParser'
                    Meta patternType metaMlConstructorRemainderParser
            else ObjectPattern <$>
                mlConstructorRemainderParser'
                    Object patternType objectMlConstructorRemainderParser
    mlConstructorRemainderParser' x patternType otherParsers =
        case patternType of
            AndPatternType -> AndPattern <$>
                binaryOperatorRemainderParser x And
            BottomPatternType -> BottomPattern <$>
                topBottomRemainderParser x Bottom
            CeilPatternType -> CeilPattern <$>
                ceilFloorRemainderParser x Ceil
            EqualsPatternType -> EqualsPattern <$>
                equalsLikeRemainderParser x Equals
            ExistsPatternType -> ExistsPattern <$>
                existsForallRemainderParser x Exists
            FloorPatternType -> FloorPattern <$>
                ceilFloorRemainderParser x Floor
            ForallPatternType -> ForallPattern <$>
                existsForallRemainderParser x Forall
            IffPatternType -> IffPattern <$>
                binaryOperatorRemainderParser x Iff
            ImpliesPatternType -> ImpliesPattern <$>
                binaryOperatorRemainderParser x Implies
            InPatternType -> InPattern <$>
                inRemainderParser x
            NotPatternType -> NotPattern <$>
                unaryOperatorRemainderParser x Not
            OrPatternType -> OrPattern <$>
                binaryOperatorRemainderParser x Or
            TopPatternType -> TopPattern <$>
                topBottomRemainderParser x Top
            _ -> otherParsers patternType
    objectMlConstructorRemainderParser patternType =
        case patternType of
            NextPatternType -> NextPattern <$>
                unaryOperatorRemainderParser Object Next
            RewritesPatternType -> RewritesPattern <$>
                binaryOperatorRemainderParser Object Rewrites
            pt ->
                fail
                    (  "Cannot have a "
                    ++ unparseToString pt
                    ++ " object pattern.")
    metaMlConstructorRemainderParser patternType =
        fail
            (  "Cannot have a "
            ++ unparseToString patternType
            ++ " meta pattern.")

{-|'patternParser' parses an unifiedPattern

BNF definitions:

@
⟨object-pattern⟩ ::=
    | ⟨object-variable⟩
    | ⟨object-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
    | ‘\and’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\not’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\or’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\implies’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\iff’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\forall’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨object-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\exists’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨object-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\ceil’ ‘{’ ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\floor’ ‘{’ ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\equals’ ‘{’ ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\in’ ‘{’ ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ pattern ‘,’ ⟨pattern⟩ ‘)’
    | ‘\top’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ‘)’
    | ‘\bottom’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ‘)’

⟨meta-pattern⟩ ::=
    | ⟨meta-variable⟩
    | ⟨char⟩
    | ⟨string⟩
    | ⟨meta-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
    | ‘\and’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\not’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\or’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\implies’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\iff’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\forall’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨meta-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\exists’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨meta-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\ceil’ ‘{’ ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\floor’ ‘{’ ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\equals’ ‘{’ ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\in’ ‘{’ ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ pattern ‘,’ ⟨pattern⟩ ‘)’
    | ‘\top’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ‘)’
    | ‘\bottom’ ‘{’ ⟨meta-sort⟩ ‘}’ ‘(’ ‘)’
@

Note that the @meta-pattern@ can be a @string@, while the @object-pattern@
can't.
-}
patternParser :: Parser UnifiedPattern
patternParser = do
    c <- Parser.peekChar'
    case c of
        '\\' -> mlConstructorParser
        '"'  -> MetaPattern . StringLiteralPattern <$> stringLiteralParser
        '\'' -> MetaPattern . CharLiteralPattern <$> charLiteralParser
        _    -> unifiedVariableOrTermPatternParser


{-|'inSquareBracketsPatternListParser' parses a @pattern-list@ delimited by
square brackets and separated by commas.

BNF definition:

@
⟨pattern-list⟩ ::= ε | ⟨pattern⟩ | ⟨pattern⟩ ‘,’ ⟨pattern-list⟩
@

BNF definition fragment for what we're parsing here:

@
⟨...⟩ ::= ... ‘[’ ⟨pattern-list⟩ ‘]’ ...
@

Always starts with @[@,
-}
inSquareBracketsPatternListParser :: Parser [UnifiedPattern]
inSquareBracketsPatternListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace
        '[' ']' ',' patternParser

{-|'inParenthesesPatternListParser' is the same as
'inSquareBracketsPatternListParser' except that it uses parentheses instead of
square brackets.
-}
inParenthesesPatternListParser :: Parser [UnifiedPattern]
inParenthesesPatternListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace
        '(' ')' ',' patternParser

{-|'attributesParser' parses an @attribute@.

BNF definition:

@
⟨attribute⟩ ::= ‘[’ ⟨pattern-list⟩ ‘]’
@

Always starts with @[@.
-}
attributesParser :: Parser Attributes
attributesParser =
    Attributes <$> inSquareBracketsPatternListParser

{-|'definitionParser' parses a Kore @definition@

BNF definition:
@
⟨definition⟩ ::= ⟨attribute⟩ ‘module’ ⟨module-name⟩ ⟨declaration⟩ ∗ ‘endmodule’ ⟨attribute⟩
@
-}
definitionParser :: Parser Definition
definitionParser =
    pure Definition
        <*> attributesParser
        <*> many1 moduleParser

{-|'moduleParser' parses the module part of a Kore @definition@

BNF definition fragment:
@
... ::= ... ‘module’ ⟨module-name⟩ ⟨declaration⟩ ∗ ‘endmodule’ ⟨attribute⟩ ...
@
-}
moduleParser :: Parser Module
moduleParser = do
    mlLexemeParser "module"
    name <- moduleNameParser
    sentences <- ParserUtils.manyUntilChar 'e' sentenceParser
    mlLexemeParser "endmodule"
    attributes <- attributesParser
    return Module
           { moduleName = name
           , moduleSentences = sentences
           , moduleAttributes = attributes
           }

{-|Enum for the sentence types that have meta- and object- versions.
-}
data SentenceType
    = AliasSentenceType
    | SymbolSentenceType


{-|'sentenceParser' parses a @declaration@.

BNF definition fragments:
@
⟨declaration⟩ ::=
    | ⟨sort-declaration⟩
    | ⟨symbol-declaration⟩
    | ⟨alias-declaration⟩
    | ⟨axiom-declaration⟩
⟨axiom-declaration⟩ ::= ‘axiom’ ...
⟨sort-declaration⟩ ::= ‘sort’ ...
⟨import-declaration⟩ ::= ‘import’ ⟨module-name⟩ ⟨attribute⟩
⟨symbol-declaration⟩ ::= ( ⟨object-symbol-declaration⟩ | ⟨meta-symbol-declaration⟩ ) ⟨attribute⟩
⟨object-symbol-declaration⟩ ::= ‘symbol’ ...
⟨meta-symbol-declaration⟩ ::= ‘symbol’ ...
⟨alias-declaration⟩ ::= ( ⟨object-alias-declaration⟩ | ⟨meta-alias-declaration⟩ ) ⟨attribute⟩
⟨object-alias-declaration⟩ ::= ‘alias’ ...
⟨meta-alias-declaration⟩ ::= ‘alias’ ...
@
-}
sentenceParser :: Parser Sentence
sentenceParser = keywordBasedParsers
    [ ( "alias", sentenceConstructorRemainderParser AliasSentenceType )
    , ( "axiom", axiomSentenceRemainderParser )
    , ( "sort", sortSentenceRemainderParser )
    , ( "symbol", sentenceConstructorRemainderParser SymbolSentenceType )
    , ( "import", importSentenceRemainderParser )
    ]
  where
    sentenceConstructorRemainderParser sentenceType = do
        c <- Parser.peekChar'
        case (c, sentenceType) of
            ('#', AliasSentenceType) -> MetaSentenceAliasSentence <$>
                aliasSymbolSentenceRemainderParser Meta (aliasParser Meta)
                    SentenceAlias
            ('#', SymbolSentenceType) -> MetaSentenceSymbolSentence <$>
                aliasSymbolSentenceRemainderParser Meta (symbolParser Meta)
                    SentenceSymbol
            (_, AliasSentenceType) -> ObjectSentenceAliasSentence <$>
                aliasSymbolSentenceRemainderParser Object (aliasParser Object)
                    SentenceAlias
            (_, SymbolSentenceType) -> ObjectSentenceSymbolSentence <$>
                aliasSymbolSentenceRemainderParser Object (symbolParser Object)
                    SentenceSymbol

{-|'aliasSymbolSentenceRemainderParser' parses the part after the starting
keyword of an alias or symbol declaration using the given head parser
to parse the head and constructs it using the given constructor.

BNF fragment example:

@
... ::=  ... ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-variable-list⟩ ‘}’
             ‘(’ ⟨object-sort-variable-list⟩ ‘)’ ‘:’ ⟨object-sort⟩ ⟨attribute⟩
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
aliasSymbolSentenceRemainderParser
    :: IsMeta a
    => a  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (m a)  -- Head parser.
    -> (m a -> [Sort a] -> Sort a -> Attributes -> as a)
    -- ^ Element constructor.
    -> Parser (as a)
aliasSymbolSentenceRemainderParser  x aliasSymbolParser constructor = do
    aliasSymbol <- aliasSymbolParser
    sorts <- inParenthesesSortListParser x
    colonParser
    resultSort <- sortParser x
    attributes <- attributesParser
    return (constructor aliasSymbol sorts resultSort attributes)

{-|'importSentenceRemainderParser' parses the part after the starting
'import' keyword of an import-declaration and constructs it.

BNF example:

@
⟨import-declaration⟩ ::= ... ⟨module-name⟩ ⟨attribute⟩
@
-}
importSentenceRemainderParser :: Parser Sentence
importSentenceRemainderParser = SentenceImportSentence <$>
    ( pure SentenceImport
        <*> moduleNameParser
        <*> attributesParser
    )

{-|'axiomSentenceRemainderParser' parses the part after the starting
'axiom' keyword of an axiom-declaration and constructs it.

BNF example:

@
⟨axiom-declaration⟩ ::= ... ‘{’ ⟨sort-variable-list⟩ ‘}’ ⟨pattern⟩ ⟨attribute⟩
@

Always starts with @{@.
-}
axiomSentenceRemainderParser :: Parser Sentence
axiomSentenceRemainderParser = SentenceAxiomSentence <$>
    ( pure SentenceAxiom
        <*> inCurlyBracesUnifiedSortVariableListParser
        <*> patternParser
        <*> attributesParser
    )

{-|'sortSentenceRemainderParser' parses the part after the starting
'sort' keyword of a sort-declaration and constructs it.

BNF example:

@
⟨sort-declaration⟩ ::= ... ‘{’ ⟨sort-variable-list⟩ ‘}’ ⟨object-sort⟩ ⟨attribute⟩
@

Always starts with @{@.
-}
sortSentenceRemainderParser :: Parser Sentence
sortSentenceRemainderParser = SentenceSortSentence <$>
    ( pure SentenceSort
        <*> idParser Object
        <*> inCurlyBracesSortVariableListParser Object
        <*> attributesParser
    )
