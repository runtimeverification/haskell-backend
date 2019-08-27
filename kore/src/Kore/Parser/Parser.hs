{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

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
   the fist two by "Variable" and the latter by "UnifiedVariable".

3. Parsers called 'Raw' receive a constructor that constructs the element.

4. Parsers called 'Reminder' receive an element's parsed prefix and an element
   constructor, parse whatever is left of the element and construct it.

5. All parsers consume the whitespace after the parsed element and expect no
   whitespace before.
-}
module Kore.Parser.Parser where

import           Control.Arrow
                 ( (&&&) )
import qualified Control.Monad as Monad
import           Text.Megaparsec
                 ( some )
import qualified Text.Megaparsec.Char as Parser
                 ( char )

import           Kore.AST.Common
import           Kore.Parser.Lexeme
import           Kore.Parser.ParserUtils
                 ( Parser )
import qualified Kore.Parser.ParserUtils as ParserUtils
import           Kore.Syntax
import           Kore.Syntax.Definition
import           Kore.Unparser
                 ( unparseToString )
import           Kore.Variables.UnifiedVariable

asParsedPattern :: (PatternF Variable) ParsedPattern -> ParsedPattern
asParsedPattern patternBase = asPattern (mempty :< patternBase)

{-|'sortVariableParser' parses either an @object-sort-variable@, or a
@meta-sort-variable@.

BNF definition:

@
⟨object-sort-variable⟩ ::= ⟨object-identifier⟩
⟨meta-sort-variable⟩ ::= ⟨meta-identifier⟩
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
sortVariableParser :: Parser SortVariable
sortVariableParser = SortVariable <$> idParser

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
objectSortParser :: Parser Sort
objectSortParser = do
    identifier <- idParser
    c <- ParserUtils.peekChar
    case c of
        Just '{' -> actualSortParser identifier
        _        -> return (SortVariableSort $ SortVariable identifier)
  where
    actualSortParser identifier = do
        sorts <- inCurlyBracesListParser objectSortParser
        return $ SortActualSort SortActual
            { sortActualName = identifier
            , sortActualSorts = sorts
            }


metaSortParser :: Parser Sort
metaSortParser = do
    sort <- keywordBasedParsers
        (map
            (show &&& return . metaSort)
            metaSortsListWithString
        )
    sorts <- inCurlyBracesListParser objectSortParser
    Monad.unless (null sorts) (fail "Expecting no parameters for meta sorts")
    return sort



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
    :: (Id -> [SortVariable] -> result)  -- ^ Element constructor.
    -> Parser result
symbolOrAliasDeclarationRawParser constructor = do
    headConstructor <- idParser
    symbolOrAliasDeclarationRemainderRawParser (constructor headConstructor)

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
    :: ([SortVariable] -> result)  -- ^ Element constructor.
    -> Parser result
symbolOrAliasDeclarationRemainderRawParser constructor =
    constructor <$> inCurlyBracesListParser sortVariableParser

{-|'aliasParser' parses either an @object-head@ or a @meta-head@ and interprets
it as an alias head.

BNF definitions:

@
⟨object-head⟩ ::= ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨meta-head⟩ ::= ⟨meta-head-constructor⟩ ‘{’ ⟨meta-sort-list⟩ ‘}’
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
aliasParser :: Parser Alias
aliasParser = symbolOrAliasDeclarationRawParser Alias


{-|'symbolParser' is the same as 'aliasParser', but it interprets the head
as a symbol one.
-}
symbolParser :: Parser Symbol
symbolParser = symbolOrAliasDeclarationRawParser Symbol

{-|'unaryOperatorRemainderParser' parses the part after an unary operator's
name and the first open curly brace and constructs it using the provided
constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
@

-}
unaryOperatorRemainderParser
    :: Parser child
    -> (Sort -> child -> result)
    -- ^ Element constructor.
    -> Parser result
unaryOperatorRemainderParser childParser constructor =
    constructor
    <$> inCurlyBracesRemainderParser objectSortParser
    <*> inParenthesesParser childParser

{-|'binaryOperatorRemainderParser' parses the part after a binary operator's
name and the first open curly brace and constructs it using the provided
constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
@

-}
binaryOperatorRemainderParser
    :: Parser child
    -> (Sort -> child -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
binaryOperatorRemainderParser childParser constructor = do
    sort <- inCurlyBracesRemainderParser objectSortParser
    (child1, child2) <- parenPairParser childParser childParser
    return (constructor sort child1 child2)

{-|'existsForallRemainderParser' parses the part after an exists or forall
operator's name and the first open curly brace and constructs it using the
provided constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ⟨object-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
@

-}
existsForallRemainderParser
    :: Parser child
    -> (Sort -> ElementVariable Variable -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
existsForallRemainderParser childParser constructor = do
    sort <- inCurlyBracesRemainderParser objectSortParser
    (variable, qChild) <- parenPairParser singletonVariableParser childParser
    return (constructor sort variable qChild)

{-|'muNuRemainderParser' parses the part after a mu or nu
operator's name and the first open curly brace and constructs it using the
provided constructor.
It uses an open recursion scheme for the children.

BNF fragment:

@
... ::= ... ‘}’ ‘(’ ⟨set-variable⟩ ‘,’ ⟨pattern⟩ ‘)’
@

-}
muNuRemainderParser
    :: Parser child
    -> (SetVariable Variable -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
muNuRemainderParser childParser constructor = do
    closedCurlyBraceParser
    (variable, qChild) <- parenPairParser setVariableParser childParser
    return (constructor variable qChild)

{-|'ceilFloorRemainderParser' parses the part after a ceil or floor
operator's name and the first open curly brace and constructs it using the
provided constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘)’
@

-}
ceilFloorRemainderParser
    :: Parser child
    -> (Sort -> Sort -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
ceilFloorRemainderParser childParser constructor = do
    (sort1, sort2) <- curlyPairRemainderParser objectSortParser
    cfChild <- inParenthesesParser childParser
    return (constructor sort1 sort2 cfChild)

{-|'equalsInRemainderParser' parses the part after an equals or in
operator's name and the first open curly brace and constructs it using the
provided constructor.
It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘,’ ⟨object-sort⟩ ‘}’ ‘(’ ⟨pattern⟩ ‘,’ ⟨pattern⟩ ‘)’
@

-}
equalsInRemainderParser
    :: Parser child
    -> (Sort -> Sort -> child -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
equalsInRemainderParser childParser constructor = do
    (sort1, sort2) <- curlyPairRemainderParser objectSortParser
    (child1, child2) <- parenPairParser childParser childParser
    return (constructor sort1 sort2 child1 child2)

{-|'topBottomRemainderParser' parses the part after a top or bottom
operator's name and the first open curly brace and constructs it using the
provided constructor.

BNF fragments:

@
... ::= ... ⟨object-sort⟩ ‘}’ ‘(’ ‘)’
@

-}
topBottomRemainderParser
    :: (Sort -> m child)  -- ^ Element constructor.
    -> Parser (m child)
topBottomRemainderParser constructor = do
    sort <- inCurlyBracesRemainderParser objectSortParser
    inParenthesesParser (return ())
    return (constructor sort)

{-|'symbolOrAliasPatternRemainderParser' parses the part after a the first
identifier in an application pattern and constructs it.
It uses an open recursion scheme for the children.

BNF fragments:

@
⟨object-pattern⟩ = ⟨object-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
⟨object-head⟩ ::= ... ‘{’ ⟨object-sort-list⟩ ‘}’

@

Always starts with @{@.
-}
symbolOrAliasPatternRemainderParser
    :: Parser child
    -> Id  -- ^ The already parsed prefix.
    -> Parser (PatternF Variable child)
symbolOrAliasPatternRemainderParser childParser identifier =
    ApplicationF
    <$> (   Application
        <$> (   SymbolOrAlias identifier
            <$> inCurlyBracesListParser objectSortParser
            )
        <*> inParenthesesListParser childParser
        )

applicationParser
    :: Parser child
    -> Parser (Application SymbolOrAlias child)
applicationParser childParser =
    Application
        <$> headParser
        <*> inParenthesesListParser childParser

{-|'variableRemainderParser' parses the part after a variable's name and
constructs it.

BNF fragments:

@
⟨object-variable⟩ ::= ... ‘:’ ⟨object-sort⟩
@

Always starts with @:@.
-}
variableRemainderParser
    :: Id  -- ^ The already parsed prefix.
    -> Parser Variable
variableRemainderParser identifier = do
    colonParser
    sort <- objectSortParser
    return Variable
        { variableName = identifier
        , variableSort = sort
        , variableCounter = mempty
        }

{-|'variableParser' parses a variable

BNF definitions:

@
⟨variable⟩ ::= ⟨identifier⟩ ‘:’ ⟨sort⟩
⟨set-variable⟩ ::= ⟨set-variable-identifier⟩ ‘:’ ⟨sort⟩
@

The @set-@ version always starts with @\@@, while the regular one does not.
-}
variableParser :: Parser Variable
variableParser = idParser >>= variableRemainderParser

singletonVariableParser :: Parser (ElementVariable Variable)
singletonVariableParser = do
    c <- ParserUtils.peekChar'
    if c == '@' then fail "Expecting singleton variable token"
    else ElementVariable <$> variableParser

setVariableParser :: Parser (SetVariable Variable)
setVariableParser = do
    c <- ParserUtils.peekChar'
    if c == '@' then SetVariable <$> variableParser
    else fail "Expecting set variable token"

{-|'variableOrTermPatternParser' parses an (object or meta) (variable pattern or
application pattern), using an open recursion scheme for its children.

BNF definitions:

@
⟨pattern⟩ ::=
    | ⟨variable⟩
    | ⟨set-variable⟩
    | ⟨object-head⟩ ‘(’ ⟨child-list⟩ ‘)’
⟨variable⟩ ::= ⟨object-identifier⟩ ‘:’ ⟨object-sort⟩
⟨set-variable⟩ ::= '\@' ⟨object-identifier⟩ ‘:’ ⟨object-sort⟩
⟨object-head⟩ ::= ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨object-head-constructor⟩ ::= ⟨object-identifier⟩
@
-}
variableOrTermPatternParser
    :: Parser child
    -> Bool  -- ^ Whether it can be a Set Variable
    -> Parser (PatternF Variable child)
variableOrTermPatternParser childParser isSetVariable = do
    identifier <- idParser
    c <- ParserUtils.peekChar'
    if c == ':'
        then do
            var <- variableRemainderParser identifier
            if isSetVariable
                then return $ VariableF (SetVar (SetVariable var))
                else return $ VariableF (ElemVar (ElementVariable var))
        else symbolOrAliasPatternRemainderParser childParser identifier


{-| parses a symbol or alias constructor and sort list
@
⟨head⟩ ::= ⟨object-head⟩ | ⟨meta-head⟩

⟨object-head⟩ ::= ⟨object-head-constructor⟩ ‘{’ ⟨object-sort-list⟩ ‘}’
⟨object-head-constructor⟩ ::= ⟨object-identifier⟩

@
-}
headParser :: Parser SymbolOrAlias
headParser =
    SymbolOrAlias
        <$> idParser
        <*> inCurlyBracesListParser objectSortParser

{-|'koreVariableOrTermPatternParser' parses a variable pattern or an
application one.

BNF definitions:

@
⟨object-pattern⟩ ::=
    | ⟨object-variable⟩
    | ⟨object-head⟩ ‘(’ ⟨pattern-list⟩ ‘)’
@
-}
koreVariableOrTermPatternParser :: Parser ParsedPattern
koreVariableOrTermPatternParser = do
    c <- ParserUtils.peekChar'
    asParsedPattern <$> variableOrTermPatternParser
        korePatternParser
        (c == '@')

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
koreMLConstructorParser :: Parser ParsedPattern
koreMLConstructorParser = do
    _ <- Parser.char '\\'
    mlPatternParser
  where
    mlPatternParser = keywordBasedParsers
        (map
            (patternString &&& koreMLConstructorRemainderParser)
            allPatternTypes
        )
    koreMLConstructorRemainderParser patternType = do
        openCurlyBraceParser
        asParsedPattern <$>
            mlConstructorRemainderParser
                korePatternParser
                domainValueParser
                patternType

{-|'leveledMLConstructorParser' is similar to 'koreMLConstructorParser'
in that it parses a pattern starting with @\@.

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
    :: Parser child
    -> Parser (DomainValue Sort child)
    -> Parser (PatternF Variable child)
leveledMLConstructorParser childParser domainValueParser' = do
    _ <- Parser.char '\\'
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
            domainValueParser'
            patternType

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
    :: Parser child
    -> Parser (DomainValue Sort child)
    -> MLPatternType
    -> Parser (PatternF Variable child)
mlConstructorRemainderParser childParser domainValueParser' patternType =
    case patternType of
        AndPatternType -> AndF <$>
            binaryOperatorRemainderParser childParser And
        BottomPatternType -> BottomF <$>
            topBottomRemainderParser Bottom
        CeilPatternType -> CeilF <$>
            ceilFloorRemainderParser childParser Ceil
        EqualsPatternType -> EqualsF <$>
            equalsInRemainderParser childParser Equals
        ExistsPatternType -> ExistsF <$>
            existsForallRemainderParser childParser Exists
        FloorPatternType -> FloorF <$>
            ceilFloorRemainderParser childParser Floor
        ForallPatternType -> ForallF <$>
            existsForallRemainderParser childParser Forall
        IffPatternType -> IffF <$>
            binaryOperatorRemainderParser childParser Iff
        ImpliesPatternType -> ImpliesF <$>
            binaryOperatorRemainderParser childParser Implies
        InPatternType -> InF <$>
            equalsInRemainderParser childParser In
        MuPatternType -> MuF <$>
            muNuRemainderParser childParser Mu
        NotPatternType -> NotF <$>
            unaryOperatorRemainderParser childParser Not
        NuPatternType -> NuF <$>
            muNuRemainderParser childParser Nu
        OrPatternType -> OrF <$>
            binaryOperatorRemainderParser childParser Or
        TopPatternType -> TopF <$>
            topBottomRemainderParser Top
        DomainValuePatternType ->
            DomainValueF <$> domainValueParser'
        NextPatternType ->
            NextF <$> unaryOperatorRemainderParser childParser Next
        RewritesPatternType ->
            RewritesF
            <$> binaryOperatorRemainderParser childParser Rewrites

domainValueParser :: Parser (DomainValue Sort ParsedPattern)
domainValueParser =
    DomainValue
        <$> inCurlyBracesRemainderParser objectSortParser
        <*> inParenthesesParser childParser
  where
    childParser = asParsedPattern . StringLiteralF <$> stringLiteralParser

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
korePatternParser :: Parser ParsedPattern
korePatternParser = do
    c <- ParserUtils.peekChar'
    case c of
        '\\' -> koreMLConstructorParser
        '"'  -> asParsedPattern . StringLiteralF <$> stringLiteralParser
        '\'' -> asParsedPattern . CharLiteralF <$> charLiteralParser
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
koreDefinitionParser :: Parser ParsedDefinition
koreDefinitionParser = definitionParser koreSentenceParser

definitionParser
    :: Parser sentence
    -> Parser (Definition sentence)
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
    :: Parser sentence
    -> Parser (Module sentence)
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
⟨hook-declararion⟩ ::= ‘hooked-sort’ ... | 'hooked-symbol' ...
@
-}
koreSentenceParser :: Parser ParsedSentence
koreSentenceParser = keywordBasedParsers
    [ ( "alias", sentenceConstructorRemainderParser AliasSentenceType )
    , ( "axiom", axiomSentenceRemainderParser SentenceAxiomSentence )
    , ( "claim", claimSentenceRemainderParser SentenceClaimSentence )
    , ( "sort", sentenceSortRemainderParser )
    , ( "symbol", sentenceConstructorRemainderParser SymbolSentenceType )
    , ( "import", importSentenceRemainderParser )
    , ( "hooked-sort", hookedSortSentenceRemainderParser )
    , ( "hooked-symbol", hookedSymbolSentenceRemainderParser )
    ]

sentenceConstructorRemainderParser
    :: SentenceType
    -> Parser ParsedSentence
sentenceConstructorRemainderParser = \case
    AliasSentenceType ->
        SentenceAliasSentence <$> aliasSentenceRemainderParser
    SymbolSentenceType ->
        SentenceSymbolSentence
        <$>
        symbolSentenceRemainderParser symbolParser SentenceSymbol

sentenceSortRemainderParser :: Parser ParsedSentence
sentenceSortRemainderParser =
  SentenceSortSentence <$> sortSentenceRemainderParser

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
    :: Parser m  -- Head parser.
    -> (m -> [Sort] -> Sort -> Attributes -> as)
    -- ^ Element constructor.
    -> Parser as
symbolSentenceRemainderParser aliasSymbolParser constructor
  = do
    aliasSymbol <- aliasSymbolParser
    sorts <- inParenthesesListParser objectSortParser
    colonParser
    resultSort <- objectSortParser
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
aliasSentenceRemainderParser :: Parser (SentenceAlias ParsedPattern)
aliasSentenceRemainderParser = do
    aliasSymbol <- aliasParser
    sorts <- inParenthesesListParser objectSortParser
    colonParser
    resultSort <- objectSortParser
    mlLexemeParser "where"
    -- Note: constraints for left pattern checked in verifySentence
    leftPattern <- applicationParser singletonVariableParser
    mlLexemeParser ":="
    rightPattern <- korePatternParser
    attributes <- attributesParser
    return
        (SentenceAlias
            aliasSymbol sorts resultSort leftPattern rightPattern attributes
        )

{-|'importSentenceRemainderParser' parses the part after the starting
'import' keyword of an import-declaration and constructs it.

BNF example:

@
⟨import-declaration⟩ ::= ... ⟨module-name⟩ ⟨attribute⟩
@
-}
importSentenceRemainderParser :: Parser ParsedSentence
importSentenceRemainderParser =
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
axiomSentenceRemainderParser
    :: ( SentenceAxiom ParsedPattern -> Sentence ParsedPattern )
    -> Parser ParsedSentence
axiomSentenceRemainderParser ctor =
  ctor
  <$> ( SentenceAxiom
        <$> inCurlyBracesListParser sortVariableParser
        <*> korePatternParser
        <*> attributesParser
      )

{-|'claimSentenceRemainderParser' parses the part after the starting
'claim' keyword of an claim declaration and constructs it.

Always starts with @{@.
-}
claimSentenceRemainderParser
    :: ( SentenceClaim ParsedPattern -> Sentence ParsedPattern )
    -> Parser ParsedSentence
claimSentenceRemainderParser ctor =
  ctor . SentenceClaim
  <$> ( SentenceAxiom
        <$> inCurlyBracesListParser sortVariableParser
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
sortSentenceRemainderParser :: Parser ParsedSentenceSort
sortSentenceRemainderParser =
    SentenceSort
    <$> idParser
    <*> inCurlyBracesListParser sortVariableParser
    <*> attributesParser

{-|'hookedSymbolSentenceRemainderParser' parses the part after the starting
@hooked-symbol@ keyword of an hook-declaration as a 'SentenceSymbol' and
constructs the corresponding 'SentenceHook'.
-}
hookedSymbolSentenceRemainderParser :: Parser ParsedSentence
hookedSymbolSentenceRemainderParser =
    (<$>)
        (SentenceHookSentence . SentenceHookedSymbol)
        (symbolSentenceRemainderParser symbolParser SentenceSymbol)

{-|'hookedSortSentenceRemainderParser' parses the part after the starting
'hooked-sort@ keyword of a sort-declaration as a 'SentenceSort' and constructs
the corresponding 'SentenceHook'.
-}
hookedSortSentenceRemainderParser :: Parser ParsedSentence
hookedSortSentenceRemainderParser =
    asSentence . SentenceHookedSort <$> sortSentenceRemainderParser

leveledPatternParser
    :: Parser child
    -> Parser (DomainValue Sort child)
    -> Parser (PatternF Variable child)
leveledPatternParser patternParser domainValueParser' = do
    c <- ParserUtils.peekChar'
    case c of
        '\\' -> leveledMLConstructorParser patternParser domainValueParser'
        '"'  -> StringLiteralF <$> stringLiteralParser
        '\'' -> CharLiteralF <$> charLiteralParser
        _ -> variableOrTermPatternParser patternParser (c == '@')

purePatternParser :: Parser ParsedPattern
purePatternParser = do
    patternHead <- leveledPatternParser childParser domainValueParser
    return $ asPattern (mempty :< patternHead)
  where
    childParser = purePatternParser
