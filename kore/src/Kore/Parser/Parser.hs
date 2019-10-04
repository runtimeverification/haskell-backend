{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Parser definition for Kore. Meant for internal use only.

Conventions used:

1. Parsers called 'Raw' receive a constructor that constructs the element.

2. Parsers called 'Reminder' receive an element's parsed prefix and an element
   constructor, parse whatever is left of the element and construct it.

3. All parsers consume the whitespace after the parsed element and expect no
   whitespace before.
-}
module Kore.Parser.Parser where

import Control.Arrow
    ( (&&&)
    )
import Text.Megaparsec
    ( some
    )

import Kore.AST.Common
import Kore.Parser.Lexeme
import Kore.Parser.ParserUtils
    ( Parser
    )
import qualified Kore.Parser.ParserUtils as ParserUtils
import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Unparser
    ( unparseToString
    )
import Kore.Variables.UnifiedVariable

asParsedPattern :: (PatternF Variable) ParsedPattern -> ParsedPattern
asParsedPattern patternBase = asPattern (mempty :< patternBase)

{-| Parses a @sort-variable@.

BNF definition:

@
<sort-variable> ::= <sort-id>
@
-}
sortVariableParser :: Parser SortVariable
sortVariableParser = SortVariable <$> sortIdParser

{-| Parses a @sort@.

BNF definition:

@
<sort>
  ::= <sort-variable>
    | <sort-id> "{" <sorts> "}"
@
-}
sortParser :: Parser Sort
sortParser = do
    identifier <- sortIdParser
    c <- ParserUtils.peekChar
    case c of
        Just '{' -> actualSortParser identifier
        _        -> return (SortVariableSort $ SortVariable identifier)
  where
    actualSortParser identifier = do
        sorts <- inCurlyBracesListParser sortParser
        return $ SortActualSort SortActual
            { sortActualName = identifier
            , sortActualSorts = sorts
            }

{-| Parses a head and constructs it using the provided constructor.

BNF definitions:

@
... ::= ... <symbol-id> "{" <sort-variables> "}" ...
@

The @meta-@ version always starts with @#@, while the @object-@ one does not.
-}
symbolOrAliasParser
    :: (Id -> [SortVariable] -> result)  -- ^ Element constructor.
    -> Parser result
symbolOrAliasParser constructor = do
    headConstructor <- symbolIdParser
    symbolOrAliasRemainderRawParser (constructor headConstructor)

{-| Parses the sort variables list that occurs alias and symbol declaration
heads and constructs the appropriate using the provided constructor.

BNF fragments:

@
... ::= ... "{" <sort-variables> "}" ...
@

Always starts with @{@.
-}
symbolOrAliasRemainderRawParser
    :: ([SortVariable] -> result)  -- ^ Element constructor.
    -> Parser result
symbolOrAliasRemainderRawParser constructor =
    constructor <$> inCurlyBracesListParser sortVariableParser

{-| Parses @symbol-or-alias@ and interprets it as an 'Alias'.

BNF definitions:

@
<alias> ::= <symbol-or-alias>
@

-}
aliasParser :: Parser Alias
aliasParser = symbolOrAliasParser Alias


{-| Parses @symbol-or-alias@ and interprets it as a 'Symbol'.

@
<symbol> ::= <symbol-or-alias>
@
-}
symbolParser :: Parser Symbol
symbolParser = symbolOrAliasParser Symbol

{-| Parses the part after an unary operator's name and the first open
curly brace and constructs it using the provided constructor.

It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨sort⟩ "}" "(" ⟨pattern⟩ ")"
@

-}
unaryOperatorRemainderParser
    :: Parser child
    -> (Sort -> child -> result)
    -- ^ Element constructor.
    -> Parser result
unaryOperatorRemainderParser childParser constructor =
    constructor
    <$> inCurlyBracesRemainderParser sortParser
    <*> inParenthesesParser childParser

{-| Parses the part after a binary operator's name and
the first open curly brace and constructs it using the provided constructor.

It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨sort⟩ "}" "(" ⟨pattern⟩ "," ⟨pattern⟩ ")"
@

-}
binaryOperatorRemainderParser
    :: Parser child
    -> (Sort -> child -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
binaryOperatorRemainderParser childParser constructor = do
    sort <- inCurlyBracesRemainderParser sortParser
    (child1, child2) <- parenPairParser childParser childParser
    return (constructor sort child1 child2)

{-| Parses the part after an @exists@ or @forall@ operator's name
and the first open curly brace and constructs it using the provided constructor.

It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨sort⟩ "}" "(" ⟨element-variable⟩ "," ⟨pattern⟩ ")"
@

-}
existsForallRemainderParser
    :: Parser child
    -> (Sort -> ElementVariable Variable -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
existsForallRemainderParser childParser constructor = do
    sort <- inCurlyBracesRemainderParser sortParser
    (variable, qChild) <- parenPairParser elementVariableParser childParser
    return (constructor sort variable qChild)

{-| Parses the part after a @mu@ or @nu@ operator's name and
the first open curly brace and constructs it using the provided constructor.

It uses an open recursion scheme for the children.

BNF fragment:

@
... ::= ... "}" "(" ⟨set-variable⟩ "," ⟨pattern⟩ ")"
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

{-| Parses the part after a ceil or floor operator's name and
the first open curly brace and constructs it using the provided constructor.

It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨sort⟩ "," ⟨sort⟩ "}" "(" ⟨pattern⟩ ")"
@

-}
ceilFloorRemainderParser
    :: Parser child
    -> (Sort -> Sort -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
ceilFloorRemainderParser childParser constructor = do
    (sort1, sort2) <- curlyPairRemainderParser sortParser
    cfChild <- inParenthesesParser childParser
    return (constructor sort1 sort2 cfChild)

{-| Parses the part after an @equals@ or @in@ operator's name and
the first open curly brace and constructs it using the provided constructor.

It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨sort⟩ "," ⟨sort⟩ "}" "(" ⟨pattern⟩ "," ⟨pattern⟩ ")"
@

-}
equalsInRemainderParser
    :: Parser child
    -> (Sort -> Sort -> child -> child -> m child)
    -- ^ Element constructor.
    -> Parser (m child)
equalsInRemainderParser childParser constructor = do
    (sort1, sort2) <- curlyPairRemainderParser sortParser
    (child1, child2) <- parenPairParser childParser childParser
    return (constructor sort1 sort2 child1 child2)

{-| Parses the part after a @top@ or @bottom@ operator's name and
the first open curly brace and constructs it using the provided constructor.

It uses an open recursion scheme for the children.

BNF fragments:

@
... ::= ... ⟨sort⟩ "}" "(" ")"
@

-}
topBottomRemainderParser
    :: (Sort -> m child)  -- ^ Element constructor.
    -> Parser (m child)
topBottomRemainderParser constructor = do
    sort <- inCurlyBracesRemainderParser sortParser
    inParenthesesParser (return ())
    return (constructor sort)

{-| Parses the part after a the first identifier in an application pattern
and constructs it.

It uses an open recursion scheme for the children.

BNF fragments:

@
<application-pattern> ::=
    ... "{" <sorts> "}" "(" <patterns> ")"
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
            <$> inCurlyBracesListParser sortParser
            )
        <*> inParenthesesListParser childParser
        )

{- | Parses an 'Application' pattern.

BNF fragments:

@
<application-pattern> ::=
    <symbol-id> "{" <sorts> "}" "(" <patterns> ")"
@
-}
applicationParser
    :: Parser child
    -> Parser (Application SymbolOrAlias child)
applicationParser childParser =
    Application
        <$> headParser
        <*> inParenthesesListParser childParser

{-| Parses the part after a variable's name and constructs it.

BNF fragments:

@
⟨...-variable⟩ ::= ... ‘:’ ⟨sort⟩
@

Always starts with @:@.
-}
variableRemainderParser
    :: Id  -- ^ The already parsed prefix.
    -> Parser Variable
variableRemainderParser identifier = do
    colonParser
    sort <- sortParser
    return Variable
        { variableName = identifier
        , variableSort = sort
        , variableCounter = mempty
        }

{- | Parses an element variable

@
<element-variable>
  ::= <element-variable-id> ":" <sort>
@
-}
elementVariableParser :: Parser (ElementVariable Variable)
elementVariableParser =
    ElementVariable <$> (elementVariableIdParser >>= variableRemainderParser)


{- | Parses an set variable

@
<set-variable>
  ::= <set-variable-id> ":" <sort>
@
-}
setVariableParser :: Parser (SetVariable Variable)
setVariableParser =
    SetVariable <$> (setVariableIdParser >>= variableRemainderParser)

{- | Parses a variable.

@
<variable>
  ::= <element-variable>
    | <set-variable>
@

Set variables always start with @\@@, while element variables do not.
-}
variableParser :: Parser (UnifiedVariable Variable)
variableParser = do
    c <- ParserUtils.peekChar'
    if c == '@'
        then SetVar  <$> setVariableParser
        else ElemVar <$> elementVariableParser

{-| Parses an element variable pattern or application pattern,
using an open recursion scheme for its children.

BNF definitions:

@
<pattern>
  ::= <element-variable>
    | <application-pattern>

⟨pattern⟩ ::=
    | ⟨element-variable⟩
    | ⟨application-pattern⟩
@
-}
elemVarOrTermPatternParser
    :: Parser child
    -> Parser (PatternF Variable child)
elemVarOrTermPatternParser childParser = do
    identifier <- idParser
    c <- ParserUtils.peekChar'
    if c == ':'
        then do
            var <- variableRemainderParser identifier
            return $ VariableF $ Const $ ElemVar $ ElementVariable var
        else symbolOrAliasPatternRemainderParser childParser identifier


{-| Parses a symbol or alias constructor and sort list
@
<application-pattern> ::=
    <symbol-id> "{" <sorts> "}" ...
@
-}
headParser :: Parser SymbolOrAlias
headParser =
    SymbolOrAlias
        <$> symbolIdParser
        <*> inCurlyBracesListParser sortParser

{-| Parses a variable pattern or an application one.

BNF definitions:

@
<pattern>
  ::= <element-variable>
    | <set-variable>
    | <application-pattern>
@
-}
koreVariableOrTermPatternParser :: Parser ParsedPattern
koreVariableOrTermPatternParser = do
    c <- ParserUtils.peekChar'
    asParsedPattern <$>
        case c of
        '@' -> do
            var <- setVariableParser
            return $ VariableF $ Const $ SetVar var
        '\\' -> do
            identifier <- symbolIdParser
            symbolOrAliasPatternRemainderParser korePatternParser identifier
        _ -> elemVarOrTermPatternParser korePatternParser

{-|'koreMLConstructorParser' parses an @ML-pattern@.

BNF definitions:

@
<ML-pattern>
  ::=
    // Predicate Logic Connectives
      "\top" "{" <sort> "}" "(" ")"
    | "\bottom" "{" <sort> "}" "(" ")"
    | "\not" "{" <sort> "}"
        "(" <pattern> ")"
    | "\and" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    | "\or" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    | "\implies" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    | "\iff" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    // FOL quantifiers
    | "\exists" "{" <sort> "}"
        "(" <element-variable> "," <pattern> ")"
    | "\forall" "{" <sort> "}"
        "(" <element-variable> "," <pattern> ")"
    // Fixpoint operators
    | "\mu" "{" <sort> "}"
        "(" <set-variable> "," <pattern> ")"
    | "\nu" "{" <sort> "}"
        "(" <set-variable> "," <pattern> ")"
    // Definedness and totality
    | "\ceil" "{" <sort> "," <sort> "}"
        "(" <pattern> ")"
    | "\floor" "{" <sort> "," <sort> "}"
        "(" <pattern> ")"
    // Equality and membership
    | "\equals" "{" <sort> "," <sort> "}"
        "(" <pattern> "," <pattern> ")"
    | "\in" "{" <sort> "," <sort> "}"
        "(" <pattern> "," <pattern> ")"
    // Transition systems
    | "\next" "{" <sort> "}"
        "(" <pattern> ")"
    | "\rewrites" "{" <sort> "}"
        "(" <pattern> "," <pattern> ")"
    // Domain values
    | "\dv" "{" <sort> "}"
        "(" <string-literal> ")"
@

Always starts with @\@.
-}
koreMLConstructorParser :: Parser ParsedPattern
koreMLConstructorParser = do
    skipChar '\\'
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

{-| Reports an error for a missing parser for a 'MLPatternType'.
-}
unsupportedPatternType
    :: Show level => level -> MLPatternType -> Parser a
unsupportedPatternType level patternType =
    fail
        (  "Cannot have a "
        ++ unparseToString patternType
        ++ " " ++ show level ++ " pattern.")

{-| A continuation parser for 'koreMLConstructorParser', called after
the constructor and the open curly brace were parsed.
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
        <$> inCurlyBracesRemainderParser sortParser
        <*> inParenthesesParser childParser
  where
    childParser =
        asParsedPattern . StringLiteralF . Const <$> stringLiteralParser

{-| Parses an pattern.

BNF definitions:

@
<pattern>
  ::= <element-variable>
    | <set-variable>
    | <ML-pattern>
    | <application-pattern>
    | <string-literal>
@
-}
korePatternParser :: Parser ParsedPattern
korePatternParser = do
    c <- ParserUtils.peekChar'
    case c of
        '\\' -> koreMLConstructorParser
        '"'  -> asParsedPattern . StringLiteralF . Const <$> stringLiteralParser
        _    -> koreVariableOrTermPatternParser

{-|'inSquareBracketsListParser' parses a @list@ of items delimited by
square brackets and separated by commas.

Always starts with @[@,
-}
inSquareBracketsListParser :: Parser item -> Parser [item]
inSquareBracketsListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '[' ']' ','

{-|'inParenthesesListParser' is the same as 'inSquareBracketsListParser'
except that it uses parentheses instead of square brackets.
-}
inParenthesesListParser :: Parser item -> Parser [item]
inParenthesesListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '(' ')' ','

{-|'inCurlyBracesListParser' is the same as 'inSquareBracketsListParser'
except that it uses curly braces instead of square brackets.
-}
inCurlyBracesListParser :: Parser item -> Parser [item]
inCurlyBracesListParser =
    ParserUtils.sepByCharWithDelimitingChars skipWhitespace '{' '}' ','

{-| Parser a (possibly empty) comma separated list of attributes enclosed in
square brackets.

BNF definition:

@
⟨attributes⟩ ::= ‘[’ ⟨patterns⟩ ‘]’
@

Always starts with @[@.
-}
attributesParser
    :: Parser Attributes
attributesParser =
    Attributes <$> inSquareBracketsListParser korePatternParser

{- | Parses a Kore @definition@

@
<definition>
  ::= <attributes> <modules_+>
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

{-|'moduleParser' parses the module part of a Kore @definition@.

BNF definition fragment:
@

<module>
  ::=   "module" <module-name-id>
            <sentences_>
        "endmodule"
        "[" <attributes> "]"
@
-}
moduleParser
    :: Parser sentence
    -> Parser (Module sentence)
moduleParser sentenceParser = do
    mlLexemeParser "module"
    name <- moduleNameIdParser
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


{-|'koreSentenceParser' parses a @sentence@.


BNF definition fragments:
@
<sentence>
  ::= <import-statement>
    | <sort-definition>
    | <hooked-sort-definition>
    | <symbol-definition>
    | <hooked-symbol-definition>
    | <axiom>
    | <claim>
    | <alias-definition>

<alias-definition> ::= "alias" ...
<axiom> ::= "axiom" ...
<claim> ::= "claim" ...
<sort-definition> ::= "sort" ...
<symbol-definition> ::= "symbol" ...
<import-statement> ::= "import" ...
<hooked-sort-definition> ::= "hooked-sort" ...
<hooked-symbol-definition> ::= "hooked-symbol" ...
@
-}
koreSentenceParser :: Parser ParsedSentence
koreSentenceParser = keywordBasedParsers
    [ ( "alias", aliasSentenceRemainderParser)
    , ( "axiom", axiomSentenceRemainderParser SentenceAxiomSentence)
    ,   ( "claim"
        , axiomSentenceRemainderParser (SentenceClaimSentence . SentenceClaim)
        )
    , ( "sort", sortSentenceRemainderParser SentenceSortSentence )
    ,   ( "hooked-sort"
        , sortSentenceRemainderParser (asSentence . SentenceHookedSort)
        )
    , ( "symbol", symbolSentenceRemainderParser SentenceSymbolSentence)
    ,   ( "hooked-symbol"
        , symbolSentenceRemainderParser (asSentence . SentenceHookedSymbol)
        )
    , ( "import", importSentenceRemainderParser )
    ]

{- | Parses the part of @symbol@ or @hooked-symbol@ after its introductory
keyword using the given constructor to construct the appropriate object.

BNF fragment example:

@
<symbol-definition>
  ::= "symbol" <symbol-id> "{" <sort-variables> "}"
        "(" <sorts> ")" ":" <sort>
        "[" <attributes> "]"
<hooked-symbol-definition>
  ::= "hooked-symbol" <symbol-id> "{" <sort-variables> "}"
        "(" <sorts> ")" ":" <sort>
        "[" <attributes> "]"
@

-}
symbolSentenceRemainderParser
    :: ( SentenceSymbol ParsedPattern -> Sentence ParsedPattern )
    -> Parser (Sentence ParsedPattern)
symbolSentenceRemainderParser ctor
  = do
    aliasSymbol <- symbolParser
    sorts <- inParenthesesListParser sortParser
    colonParser
    resultSort <- sortParser
    attributes <- attributesParser
    return (ctor $ SentenceSymbol aliasSymbol sorts resultSort attributes)


{-| Parses the part after the starting keyword of an alias declaration.

BNF fragment example:

@
<alias-definition>
  ::= "alias" <symbol-id> "{" <sort-variables> "}"
        "(" <sorts> ")" ":" <sort>
        "where" <application-pattern> ":=" <pattern>
        "[" <attributes> "]"
@

-}
aliasSentenceRemainderParser :: Parser (Sentence ParsedPattern)
aliasSentenceRemainderParser = do
    aliasSymbol <- aliasParser
    sorts <- inParenthesesListParser sortParser
    colonParser
    resultSort <- sortParser
    mlLexemeParser "where"
    -- Note: constraints for left pattern checked in verifySentence
    leftPattern <- applicationParser variableParser
    mlLexemeParser ":="
    rightPattern <- korePatternParser
    attributes <- attributesParser
    return
        (SentenceAliasSentence $ SentenceAlias
            aliasSymbol sorts resultSort leftPattern rightPattern attributes
        )

{- | Parses the part after the starting 'import' keyword of an
import-declaration and constructs it.

BNF example:

@
<import-statement>
  ::= "import" <module-name-id>
        "[" <attributes> "]"
@
-}
importSentenceRemainderParser :: Parser ParsedSentence
importSentenceRemainderParser =
    SentenceImportSentence
    <$> ( SentenceImport
          <$> moduleNameIdParser
          <*> attributesParser
        )

{- | Parses the part of @axiom@ or @claim@ after its introductory
keyword using the given constructor to construct the appropriate object.

BNF example:

@
<axiom>
  ::= "axiom" "{" <sort-variables> "}"
        <pattern>
        "[" <attributes> "]"
<claim>
  ::= "claim" "{" <sort-variables> "}"
        <pattern>
        "[" <attributes> "]"
@

-}
axiomSentenceRemainderParser
    :: (SentenceAxiom ParsedPattern -> ParsedSentence)
    -> Parser ParsedSentence
axiomSentenceRemainderParser ctor =
    ctor <$>
        ( SentenceAxiom
            <$> inCurlyBracesListParser sortVariableParser
            <*> korePatternParser
            <*> attributesParser
        )

{- | Parses the part of @sort@ or @hooked-sort@ after its introductory
keyword using the given constructor to construct the appropriate object.

BNF example:

@
<sort-definition>
  ::= "sort" <sort-id> "{" <sort-variables> "}"
        "[" <attributes> "]"
<hooked-sort-definition>
  ::= "hooked-sort" <sort-id> "{" <sort-variables> "}"
        "[" <attributes> "]"
@

-}
sortSentenceRemainderParser
    :: (SentenceSort ParsedPattern -> ParsedSentence)
    -> Parser ParsedSentence
sortSentenceRemainderParser ctor =
    ctor <$>
        (SentenceSort
            <$> sortIdParser
            <*> inCurlyBracesListParser sortVariableParser
            <*> attributesParser
        )


