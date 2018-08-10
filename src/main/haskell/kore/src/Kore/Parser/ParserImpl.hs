{-|
Module      : Kore.Parser.ParserImpl
Description : Parser definition for Kore. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Parser definition for Kore. Meant for internal use only.

Conventions used:

1. In various cases we distinguish between @object-@ and @meta-@ versions of an
   element. For this we parametrize the element's type with a @level@ and we
   provide an element of type @level@ to the parser, usually called @x@.

2. The meta versions are identified by the presence of @#@ characters, usually
   found at the start of the element. However, when they are found inside,
   we may split the parser in two pieces, one that parses everything until the
   first element that may start with @#@ and identifies the value of @x@ and
   another one that receives 'x' and parses the reminder.

3. Whenever we have both an element which can be meta or object and
   an element which is the union of the two, the union is called 'Unified*'.
   As an example, if we have @⟨object-variable⟩@, @⟨meta-variable⟩@ and
   @⟨variable⟩ ::= ⟨object-variable⟩ | ⟨meta-variable⟩@, then we'll represent
   the fist two by "Variable level" and the latter by "UnifiedVariable".

3. Parsers called 'Raw' receive a constructor that constructs the element.

4. Parsers called 'Reminder' receive an element's parsed prefix and an element
   constructor, parse whatever is left of the element and construct it.

5. All parsers consume the whitespace after the parsed element and expect no
   whitespace before.
-}
module Kore.Parser.ParserImpl where

import           Control.Arrow
                 ( (&&&) )
import           Control.Monad
                 ( unless, void )
import           Data.Functor.Foldable
import           Data.Maybe
                 ( isJust )
import           Text.Megaparsec
                 ( some )
import qualified Text.Megaparsec.Char as Parser
                 ( char )

import           Data.Function.Compose
                 ( (<....>) )
import           Data.Functor.Impredicative
                 ( Rotate31 (..) )
import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.AST.Sentence
import           Kore.MetaML.AST
import           Kore.Parser.Lexeme
import           Kore.Parser.ParserUtils
                 ( Parser )
import qualified Kore.Parser.ParserUtils as ParserUtils
import           Kore.Unparser.Unparse

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
    :: MetaOrObject level
    => level        -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (SortVariable level)
sortVariableParser x = SortVariable <$> idParser x

{-|'unifiedSortVariableParser' parses a sort variable.-}
unifiedSortVariableParser :: Parser UnifiedSortVariable
unifiedSortVariableParser = do
    c <- ParserUtils.peekChar'
    if c == '#'
        then UnifiedMeta <$> sortVariableParser Meta
        else UnifiedObject <$> sortVariableParser Object

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
    :: MetaOrObject level
    => level        -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (Sort level)
sortParser x = do
    identifier <- idParser x
    c <- ParserUtils.peekChar
    case c of
        Just '{' -> actualSortParser identifier
        _        -> return (SortVariableSort $ SortVariable identifier)
  where
    actualSortParser identifier = do
        sorts <- inCurlyBracesListParser (sortParser x)
        return $ SortActualSort SortActual
            { sortActualName = stringNameNormalizer identifier
            , sortActualSorts = sorts
            }
    stringNameNormalizer :: Id level -> Id level
    stringNameNormalizer identifier@Id {getId = i} =
        if isMeta x && (i == show StringSort)
            then identifier
                { getId = show (MetaListSortType CharSort) }
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
    :: MetaOrObject level
    => Id level     -- ^ The sort name
    -> [Sort level] -- ^ The sort arguments
    -> Parser ()
validateMetaSort identifier [] =
    unless (isJust (metaSortConverter metaId))
        (fail ("metaSortConverter: Invalid constructor: '" ++ metaId ++ "'."))
  where
    metaId = getId identifier
validateMetaSort _ _ = fail "metaSortConverter: Non empty parameter sorts."

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
    :: MetaOrObject level
    => level  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Id level -> [SortVariable level] -> m level)  -- ^ Element constructor.
    -> Parser (m level)
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
    :: MetaOrObject level
    => level   -- ^ Distinguishes between the meta and non-meta elements.
    -> ([SortVariable level] -> m level)  -- ^ Element constructor.
    -> Parser (m level)
symbolOrAliasDeclarationRemainderRawParser x constructor =
    constructor <$> inCurlyBracesListParser (sortVariableParser x)

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
    :: MetaOrObject level
    => level        -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (Alias level)
aliasParser x = symbolOrAliasDeclarationRawParser x Alias


{-|'symbolParser' is the same as 'aliasParser', but it interprets the head
as a symbol one.
-}
symbolParser :: MetaOrObject level => level -> Parser (Symbol level)
symbolParser x = symbolOrAliasDeclarationRawParser x Symbol

{-|'unaryOperatorRemainderParser' parses the part after an unary operator's
name and the first open curly brace and constructs it using the provided
constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
unaryOperatorRemainderParser
    :: MetaOrObject level
    => Parser child
    -> level  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort level -> child -> m level child)
    -- ^ Element constructor.
    -> Parser (m level child)
unaryOperatorRemainderParser childParser x constructor =
    constructor
    <$> inCurlyBracesRemainderParser (sortParser x)
    <*> inParenthesesParser childParser

{-|'binaryOperatorRemainderParser' parses the part after a binary operator's
name and the first open curly brace and constructs it using the provided
constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
binaryOperatorRemainderParser
    :: MetaOrObject level
    => Parser child
    -> level  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort level -> child -> child -> m level child)
    -- ^ Element constructor.
    -> Parser (m level child)
binaryOperatorRemainderParser childParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    (child1, child2) <-
        parenPairParser childParser childParser
    return (constructor sort child1 child2)

{-|'existsForallRemainderParser' parses the part after an exists or forall
operator's name and the first open curly brace and constructs it using the
provided constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨object-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘}’ ‘(’ ⟨meta-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
existsForallRemainderParser
    :: MetaOrObject level
    => Parser child
    -> level  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort level -> Variable level -> child
        -> m level Variable child)
    -- ^ Element constructor.
    -> Parser (m level Variable child)
existsForallRemainderParser childParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    (variable, qChild) <- parenPairParser (variableParser x) childParser
    return (constructor sort variable qChild)

{-|'ceilFloorRemainderParser' parses the part after a ceil or floor
operator's name and the first open curly brace and constructs it using the
provided constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
ceilFloorRemainderParser
    :: MetaOrObject level
    => Parser child
    -> level  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort level -> Sort level -> child -> m level child)
    -- ^ Element constructor.
    -> Parser (m level child)
ceilFloorRemainderParser childParser x constructor = do
    (sort1, sort2) <- curlyPairRemainderParser (sortParser x)
    cfChild <- inParenthesesParser childParser
    return (constructor sort1 sort2 cfChild)

{-|'equalsInRemainderParser' parses the part after an equals or in
operator's name and the first open curly brace and constructs it using the
provided constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
... ::= ... ⟨meta-sort⟩ ‘,’ ⟨meta-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
equalsInRemainderParser
    :: MetaOrObject level
    => Parser child
    -> level  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort level -> Sort level -> child -> child -> m level child)
    -- ^ Element constructor.
    -> Parser (m level child)
equalsInRemainderParser childParser x constructor = do
    (sort1, sort2) <- curlyPairRemainderParser (sortParser x)
    (child1, child2) <-
        parenPairParser childParser childParser
    return (constructor sort1 sort2 child1 child2)

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
    :: MetaOrObject level
    => level  -- ^ Distinguishes between the meta and non-meta elements.
    -> (Sort level -> m level child)  -- ^ Element constructor.
    -> Parser (m level child)
topBottomRemainderParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    inParenthesesParser (return ())
    return (constructor sort)

{-|'symbolOrAliasPatternRemainderParser' parses the part after a the first
identifier in an application pattern and constructs it.
It uses an open recursion scheme for the children.

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
    :: MetaOrObject level
    => Parser child
    -> level  -- ^ Distinguishes between the meta and non-meta elements.
    -> Id level  -- ^ The already parsed prefix.
    -> Parser (Pattern level Variable child)
symbolOrAliasPatternRemainderParser childParser x identifier =
    ApplicationPattern
    <$> (   Application
        <$> (   SymbolOrAlias identifier
            <$> inCurlyBracesListParser (sortParser x)
            )
        <*> inParenthesesListParser childParser
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
    :: MetaOrObject level
    => level  -- ^ Distinguishes between the meta and non-meta elements.
    -> Id level  -- ^ The already parsed prefix.
    -> Parser (Variable level)
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
    :: MetaOrObject level
    => level  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (Variable level)
variableParser x = idParser x >>= variableRemainderParser x

{-|'unifiedVariableParser' parses a @variable@.

BNF definitions:

@
⟨variable⟩ ::= ⟨object-variable⟩ | ⟨meta-variable⟩
@
unifiedVariableParser :: Parser (UnifiedVariable Variable)
unifiedVariableParser = do
    c <- ParserUtils.peekChar'
    if c == '#'
        then MetaVariable <$> variableParser Meta
        else ObjectVariable <$> variableParser Object
-}

{-|'variableOrTermPatternParser' parses an (object or meta) (variable pattern or
application pattern), using an open recursion scheme for its children.

BNF definitions:

@
⟨object-pattern⟩ ::=
    | ⟨object-variable⟩
    | ⟨object-head⟩ ‘(’ ⟨child-list⟩ ‘)’
⟨object-variable⟩ ::= ⟨object-identifier⟩ ‘:’ ⟨object-sort⟩
⟨object-head⟩ ::= ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨object-head-constructor⟩ ::= ⟨object-identifier⟩

⟨meta-pattern⟩ ::=
    | ⟨meta-variable⟩
    | ⟨meta-head⟩ ‘(’ ⟨child-list⟩ ‘)’
⟨meta-variable⟩ ::= ⟨meta-identifier⟩ ‘:’ ⟨meta-sort⟩
⟨meta-head⟩ ::= ⟨meta-head-constructor⟩ ‘{’ ⟨meta-sort-list⟩ ‘}’
⟨meta-head-constructor⟩ ::= ⟨meta-identifier⟩
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
variableOrTermPatternParser
    :: MetaOrObject level
    => Parser child
    -> level  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (Pattern level Variable child)
variableOrTermPatternParser childParser x = do
    identifier <- idParser x
    c <- ParserUtils.peekChar'
    if c == ':'
        then VariablePattern <$> variableRemainderParser x identifier
        else symbolOrAliasPatternRemainderParser childParser x identifier


{-| parses a symbol or alias constructor and sort list
@
⟨head⟩ ::= ⟨object-head⟩ | ⟨meta-head⟩

⟨object-head⟩ ::= ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨object-head-constructor⟩ ::= ⟨object-identifier⟩

⟨meta-head⟩ ::= ⟨meta-head-constructor⟩ ‘{’ ⟨meta-sort-list⟩ ‘}’
⟨meta-head-constructor⟩ ::= ⟨meta-identifier⟩
@
-}
headParser
    :: MetaOrObject level
    => level  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (SymbolOrAlias level)
headParser x = do
    identifier <- idParser x
    (SymbolOrAlias identifier <$> inCurlyBracesListParser (sortParser x))

{-|'koreVariableOrTermPatternParser' parses a variable pattern or an
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
koreVariableOrTermPatternParser :: Parser CommonKorePattern
koreVariableOrTermPatternParser = do
    c <- ParserUtils.peekChar'
    if c == '#'
        then
            asKorePattern <$> variableOrTermPatternParser
                korePatternParser
                Meta
        else
            asKorePattern <$> variableOrTermPatternParser
                korePatternParser
                Object

{-|'koreMLConstructorParser' parses a pattern starting with @\@.

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
    | ‘\dv’ ‘{’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
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
koreMLConstructorParser :: Parser CommonKorePattern
koreMLConstructorParser = do
    void (Parser.char '\\')
    mlPatternParser
  where
    mlPatternParser = keywordBasedParsers
        (map
            (patternString &&& koreMLConstructorRemainderParser)
            allPatternTypes
        )
    koreMLConstructorRemainderParser patternType = do
        openCurlyBraceParser
        c <- ParserUtils.peekChar'
        if c == '#'
            then asKorePattern <$>
                mlConstructorRemainderParser korePatternParser
                    Meta patternType (unsupportedPatternType Meta)
            else asKorePattern <$>
                mlConstructorRemainderParser korePatternParser
                    Object patternType objectMlConstructorRemainderParser
    objectMlConstructorRemainderParser patternType =
        case patternType of
            DomainValuePatternType -> DomainValuePattern <$>
                (   DomainValue
                <$> inCurlyBracesRemainderParser (sortParser Object)
                <*> inParenthesesParser (purePatternParser Meta)
                )
            NextPatternType -> NextPattern <$>
                unaryOperatorRemainderParser korePatternParser Object Next
            RewritesPatternType -> RewritesPattern <$>
                binaryOperatorRemainderParser
                    korePatternParser
                    Object
                    Rewrites
            pt -> unsupportedPatternType Object pt

{-|'leveledMLConstructorParser' is similar to 'koreMLConstructorParser'
in that it parses a pattern starting with @\@.  However, it only parses
patterns types which can belong to both 'Meta' and 'Object' categories, and
returns an object of the 'Pattern' type.

BNF definitions (here cat ranges over meta and object):

@
⟨cat-pattern⟩ ::=
    | ‘\and’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\not’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\or’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\implies’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\iff’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\forall’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨cat-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\exists’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨cat-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\ceil’ ‘{’ ⟨cat-sort⟩ ‘,’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\floor’ ‘{’ ⟨cat-sort⟩ ‘,’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
    | ‘\equals’ ‘{’ ⟨cat-sort⟩ ‘,’ ⟨cat-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
    | ‘\in’ ‘{’ ⟨cat-sort⟩ ‘,’ ⟨cat-sort⟩ ‘}’ ‘(’ pattern ‘,’ ⟨pattern⟩ ‘)’
    | ‘\top’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ‘)’
    | ‘\bottom’ ‘{’ ⟨cat-sort⟩ ‘}’ ‘(’ ‘)’
@
-}
leveledMLConstructorParser
    :: MetaOrObject level
    => Parser child
    -> level
    -> Parser (Pattern level Variable child)
leveledMLConstructorParser childParser level = do
    void (Parser.char '\\')
    keywordBasedParsers
        (map
            (patternString &&& leveledMLConstructorRemainderParser)
            allPatternTypes
        )
  where
    leveledMLConstructorRemainderParser patternType = do
        openCurlyBraceParser
        mlConstructorRemainderParser
            childParser
            level
            patternType
            (unsupportedPatternType level)

{-|'unsupportedPatternType' reports an error for a missing parser for
a 'MLPatternType'.
-}
unsupportedPatternType
    :: Show level => level -> MLPatternType -> Parser a
unsupportedPatternType level patternType =
    fail
        (  "Cannot have a "
        ++ unparseToString patternType
        ++ " " ++ show level ++ " pattern.")

{-|'mlConstructorRemainderParser' represents a continuation parser for
'leveledMLConstructorParser', called after the constructor and the open curly
brace were parsed. Note that parsing the constructor and open curly brace is
required to be able to peek at the first character of the sort identifier, in
order to determine whether we are parsing a 'Meta' or an 'Object' 'Pattern'.
-}
mlConstructorRemainderParser
    :: MetaOrObject level
    => Parser child
    -> level
    -> MLPatternType
    -> (MLPatternType -> Parser (Pattern level Variable child))
    -> Parser (Pattern level Variable child)
mlConstructorRemainderParser childParser x patternType otherParsers =
    case patternType of
        AndPatternType -> AndPattern <$>
            binaryOperatorRemainderParser childParser x And
        BottomPatternType -> BottomPattern <$>
            topBottomRemainderParser x Bottom
        CeilPatternType -> CeilPattern <$>
            ceilFloorRemainderParser childParser x Ceil
        EqualsPatternType -> EqualsPattern <$>
            equalsInRemainderParser childParser x Equals
        ExistsPatternType -> ExistsPattern <$>
            existsForallRemainderParser childParser x Exists
        FloorPatternType -> FloorPattern <$>
            ceilFloorRemainderParser childParser x Floor
        ForallPatternType -> ForallPattern <$>
            existsForallRemainderParser childParser x Forall
        IffPatternType -> IffPattern <$>
            binaryOperatorRemainderParser childParser x Iff
        ImpliesPatternType -> ImpliesPattern <$>
            binaryOperatorRemainderParser childParser x Implies
        InPatternType -> InPattern <$>
            equalsInRemainderParser childParser x In
        NotPatternType -> NotPattern <$>
            unaryOperatorRemainderParser childParser x Not
        OrPatternType -> OrPattern <$>
            binaryOperatorRemainderParser childParser x Or
        TopPatternType -> TopPattern <$>
            topBottomRemainderParser x Top
        _ -> otherParsers patternType

{-|'korePatternParser' parses an unifiedPattern

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
korePatternParser :: Parser CommonKorePattern
korePatternParser = do
    c <- ParserUtils.peekChar'
    case c of
        '\\' -> koreMLConstructorParser
        '"'  -> asKorePattern . StringLiteralPattern <$> stringLiteralParser
        '\'' -> asKorePattern . CharLiteralPattern <$> charLiteralParser
        _    -> koreVariableOrTermPatternParser

{-|'inSquareBracketsListParser' parses a @list@ of items delimited by
square brackets and separated by commas.

Always starts with @[@,
-}
inSquareBracketsListParser :: Parser item -> Parser [item]
inSquareBracketsListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '[' ']' ','

{-|'inParenthesesListParser' is the same as
'inSquareBracketsListParser' except that it uses parentheses instead of
square brackets.
-}
inParenthesesListParser :: Parser item -> Parser [item]
inParenthesesListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '(' ')' ','

{-|'inCurlyBracesListParser' is the same as
'inSquareBracketsListParser' except that it uses curly braces instead of
square brackets.
-}
inCurlyBracesListParser :: Parser item -> Parser [item]
inCurlyBracesListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '{' '}' ','

{-|'attributesParser' parses an @attribute@.

BNF definition:

@
⟨attribute⟩ ::= ‘[’ ⟨pattern-list⟩ ‘]’
@

Always starts with @[@.
-}
attributesParser
    :: Parser Attributes
attributesParser =
    Attributes <$> inSquareBracketsListParser korePatternParser

{-|'koreDefinitionParser' parses a Kore @definition@

BNF definition:
@
⟨definition⟩ ::= ⟨attribute⟩ ‘module’ ⟨module-name⟩ ⟨declaration⟩ ∗ ‘endmodule’ ⟨attribute⟩
@
-}
koreDefinitionParser :: Parser KoreDefinition
koreDefinitionParser = definitionParser koreSentenceParser

definitionParser
    :: Parser (sentence sortParam pat variable)
    -> Parser (Definition sentence sortParam pat variable)
definitionParser sentenceParser =
  Definition
  <$> attributesParser
  <*> some (moduleParser sentenceParser)

{-|'moduleParser' parses the module part of a Kore @definition@

BNF definition fragment:
@
... ::= ... ‘module’ ⟨module-name⟩ ⟨declaration⟩ ∗ ‘endmodule’ ⟨attribute⟩ ...
@
-}
moduleParser
    :: Parser (sentence sortParam pat variable)
    -> Parser (Module sentence sortParam pat variable)
moduleParser sentenceParser = do
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


{-|'koreSentenceParser' parses a @declaration@.

BNF definition fragments:
@
⟨declaration⟩ ::=
    | ⟨import-declaration⟩
    | ⟨sort-declaration⟩
    | ⟨symbol-declaration⟩
    | ⟨alias-declaration⟩
    | ⟨axiom-declaration⟩
    | ⟨hook-declaration⟩
⟨axiom-declaration⟩ ::= ‘axiom’ ...
⟨sort-declaration⟩ ::= ‘sort’ ...
⟨import-declaration⟩ ::= ‘import’ ⟨module-name⟩ ⟨attribute⟩
⟨symbol-declaration⟩ ::= ( ⟨object-symbol-declaration⟩ | ⟨meta-symbol-declaration⟩ ) ⟨attribute⟩
⟨object-symbol-declaration⟩ ::= ‘symbol’ ...
⟨meta-symbol-declaration⟩ ::= ‘symbol’ ...
⟨alias-declaration⟩ ::= ( ⟨object-alias-declaration⟩ | ⟨meta-alias-declaration⟩ ) ⟨attribute⟩
⟨object-alias-declaration⟩ ::= ‘alias’ ...
⟨meta-alias-declaration⟩ ::= ‘alias’ ...
⟨hook-declararion⟩ ::= ‘hooked-sort ... | 'hooked-symbol' ...
@
-}
koreSentenceParser :: Parser KoreSentence
koreSentenceParser = keywordBasedParsers
    [ ( "alias", sentenceConstructorRemainderParser AliasSentenceType )
    , ( "axiom", axiomSentenceRemainderParser )
    , ( "sort", sentenceSortRemainderParser )
    , ( "symbol", sentenceConstructorRemainderParser SymbolSentenceType )
    , ( "import", importSentenceRemainderParser )
    , ( "hooked-sort", hookedSortSentenceRemainderParser )
    , ( "hooked-symbol", hookedSymbolSentenceRemainderParser )
    ]

sentenceConstructorRemainderParser :: SentenceType -> Parser KoreSentence
sentenceConstructorRemainderParser sentenceType
      = do
        c <- ParserUtils.peekChar'
        case (c, sentenceType) of
            ('#', AliasSentenceType) ->
                constructUnifiedSentence SentenceAliasSentence . unRotate31
                <$>
                aliasSentenceRemainderParser Meta
            ('#', SymbolSentenceType) ->
                constructUnifiedSentence SentenceSymbolSentence . unRotate31
                <$>
                symbolSentenceRemainderParser
                    Meta
                    (symbolParser Meta)
                    (Rotate31 <....> SentenceSymbol)
            (_, AliasSentenceType) ->
                constructUnifiedSentence SentenceAliasSentence . unRotate31
                <$>
                aliasSentenceRemainderParser Object
            (_, SymbolSentenceType) ->
                constructUnifiedSentence SentenceSymbolSentence . unRotate31
                <$>
                symbolSentenceRemainderParser
                    Object
                    (symbolParser Object)
                    (Rotate31 <....> SentenceSymbol)

sentenceSortRemainderParser :: Parser KoreSentence
sentenceSortRemainderParser = do
  c <- ParserUtils.peekChar'
  case c of
    '#' -> constructUnifiedSentence SentenceSortSentence
           <$> sortSentenceRemainderParser Meta
    _   -> constructUnifiedSentence SentenceSortSentence
           <$> sortSentenceRemainderParser Object

{-|'symbolSentenceRemainderParser' parses the part after the starting
keyword of an alias or symbol declaration using the given head parser
to parse the head and constructs it using the given constructor.

BNF fragment example:

@
... ::=  ... ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-variable-list⟩ ‘}’
             ‘(’ ⟨object-sort-variable-list⟩ ‘)’ ‘:’ ⟨object-sort⟩ ⟨attribute⟩
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
symbolSentenceRemainderParser
    :: MetaOrObject level
    => level  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser (m level)  -- Head parser.
    -> (m level
        -> [Sort level]
        -> Sort level
        -> Attributes
        -> as level
       )
    -- ^ Element constructor.
    -> Parser (as level)
symbolSentenceRemainderParser  x aliasSymbolParser constructor
  = do
    aliasSymbol <- aliasSymbolParser
    sorts <- inParenthesesListParser (sortParser x)
    colonParser
    resultSort <- sortParser x
    attributes <- attributesParser
    return (constructor aliasSymbol sorts resultSort attributes)


{-|'aliasSentenceRemainderParser' parses the part after the starting
keyword of an alias declaration.

BNF fragment example:

@
... ::=  `alias` ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-variable-list⟩ ‘}’ ‘(’ ⟨object-sort-list⟩ ‘)’ ‘:’ ⟨object-sort⟩ ⟨attribute⟩
         `where` ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-variable-list⟩ ‘}’ ‘(’ ⟨object-variable-list⟩ ‘)’ `:=` ⟨object-pattern⟩
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
aliasSentenceRemainderParser
    :: MetaOrObject level
    => level  -- ^ Distinguishes between the meta and non-meta elements.
    -> Parser ((Rotate31 SentenceAlias UnifiedPattern Variable) level)
aliasSentenceRemainderParser x
  = do
    aliasSymbol <- (aliasParser x)
    sorts <- inParenthesesListParser (sortParser x)
    colonParser
    resultSort <- sortParser x
    mlLexemeParser "where"
    -- Note: constraints for left pattern checked in verifySentence
    leftPattern <- leveledPatternParser korePatternParser x
    mlLexemeParser ":="
    rightPattern <- leveledPatternParser korePatternParser x
    attributes <- attributesParser
    return (Rotate31 (SentenceAlias aliasSymbol sorts resultSort leftPattern rightPattern attributes))

{-|'importSentenceRemainderParser' parses the part after the starting
'import' keyword of an import-declaration and constructs it.

BNF example:

@
⟨import-declaration⟩ ::= ... ⟨module-name⟩ ⟨attribute⟩
@
-}
importSentenceRemainderParser :: Parser KoreSentence
importSentenceRemainderParser =
    constructUnifiedSentence
    SentenceImportSentence
    <$> ( SentenceImport
          <$> moduleNameParser
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
axiomSentenceRemainderParser :: Parser KoreSentence
axiomSentenceRemainderParser =
  asSentence
  <$> ( SentenceAxiom
        <$> inCurlyBracesListParser unifiedSortVariableParser
        <*> korePatternParser
        <*> attributesParser
      )

{-|'sortSentenceRemainderParser' parses the part after the starting
@sort@ keyword of a sort-declaration and constructs it.

BNF example:

@
⟨sort-declaration⟩ ::= ... ‘{’ ⟨sort-variable-list⟩ ‘}’ ⟨object-sort⟩ ⟨attribute⟩
@

Always starts with @{@.
-}
sortSentenceRemainderParser
  :: MetaOrObject level
  => level
  -> Parser (KoreSentenceSort level)
sortSentenceRemainderParser x =
    SentenceSort
    <$> idParser x
    <*> inCurlyBracesListParser (sortVariableParser x)
    <*> attributesParser

{-|'hookedSymbolSentenceRemainderParser' parses the part after the starting
@hooked-symbol@ keyword of an hook-declaration as a 'SentenceSymbol' and
constructs the corresponding 'SentenceHook'.
-}
hookedSymbolSentenceRemainderParser :: Parser KoreSentence
hookedSymbolSentenceRemainderParser =
    constructUnifiedSentence SentenceHookSentence . SentenceHookedSymbol . unRotate31
    <$> symbolSentenceRemainderParser
    Object
    (symbolParser Object)
    (Rotate31 <....> SentenceSymbol)

{-|'hookedSortSentenceRemainderParser' parses the part after the starting
'hooked-sort@ keyword of a sort-declaration as a 'SentenceSort' and constructs
the corresponding 'SentenceHook'.
-}
hookedSortSentenceRemainderParser :: Parser KoreSentence
hookedSortSentenceRemainderParser =
    asSentence . SentenceHookedSort <$> sortSentenceRemainderParser Object

leveledPatternParser
    :: MetaOrObject level
    => Parser child
    -> level
    -> Parser (Pattern level Variable child)
leveledPatternParser patternParser level = do
    c <- ParserUtils.peekChar'
    case c of
        '\\' -> leveledMLConstructorParser patternParser level
        _ -> case isMetaOrObject (toProxy level) of
            IsMeta -> case c of
                '"'  -> StringLiteralPattern <$> stringLiteralParser
                '\'' -> CharLiteralPattern <$> charLiteralParser
                _    -> variableOrTermPatternParser patternParser Meta
            IsObject -> variableOrTermPatternParser patternParser Object

purePatternParser
    :: MetaOrObject level
    => level
    -> Parser (CommonPurePattern level)
purePatternParser level =
    Fix <$> leveledPatternParser (purePatternParser level) level

metaPatternParser :: Parser CommonMetaPattern
metaPatternParser = purePatternParser Meta
