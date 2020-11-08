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
module Kore.Parser.Parser
    ( koreDefinitionParser
    , parsePattern
    , embedParsedPattern
    , parseAliasHead, parseSymbolHead
    , parseSortVariable
    , parseSort
    , attributesParser
    , koreSentenceParser
    , moduleParser
    , definitionParser
    , parseArguments
    , parseParameters
    , parseElementVariable
    , parseSetVariable
    , parseVariableCounter
    ) where

import Prelude.Kore hiding
    ( many
    , some
    )

import qualified Control.Monad as Monad
import qualified Data.Char as Char
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Text.Megaparsec
    ( some
    , (<?>)
    )
import qualified Text.Megaparsec as Parse

import Data.Sup
import Kore.Parser.Lexeme
import Kore.Parser.ParserUtils
    ( Parser
    )
import qualified Kore.Parser.ParserUtils as ParserUtils
import Kore.Syntax
import Kore.Syntax.Definition
import Numeric.Natural

embedParsedPattern :: (PatternF VariableName) ParsedPattern -> ParsedPattern
embedParsedPattern patternBase = asPattern (mempty :< patternBase)

{- | Parses a @sort-variable@.

BNF definition:

@
<sort-variable> ::= <sort-id>
@
-}
parseSortVariable :: Parser SortVariable
parseSortVariable = SortVariable <$> parseSortId

{- | Parses a @sort@.

BNF definition:

@
<sort> ::= <sort-variable> | <sort-id> "{" <sorts> "}"
@
-}
parseSort :: Parser Sort
parseSort = do
    identifier <- parseSortId
    parseRemainder identifier
  where
    parseRemainder ident =
        (SortActualSort <$> parseSortActualRemainder ident)
        <|> (SortVariableSort <$> parseSortVariableRemainder ident)

parseSortActualRemainder :: Id -> Parser SortActual
parseSortActualRemainder sortActualName = do
    sortActualSorts <- parseParameters parseSort
    pure SortActual { sortActualName, sortActualSorts }

parseSortVariableRemainder :: Id -> Parser SortVariable
parseSortVariableRemainder = pure . SortVariable

{- | Parses the head of a symbol or alias declaration.

BNF definitions:

@
... ::= ... <symbol-id> "{" <sort-variables> "}" ...
@

-}
parseSymbolOrAliasDeclarationHead
    :: (Id -> [SortVariable] -> head)  -- ^ head constructor
    -> Parser head
parseSymbolOrAliasDeclarationHead mkHead = do
    identifier <- parseSymbolId
    parameters <- parseParameters parseSortVariable
    pure (mkHead identifier parameters)

{-| Parses @symbol-or-alias@ and interprets it as an 'Alias'.

BNF definitions:

@
<alias> ::= <symbol-or-alias>
@

-}
parseAliasHead :: Parser Alias
parseAliasHead = parseSymbolOrAliasDeclarationHead Alias


{-| Parses @symbol-or-alias@ and interprets it as a 'Symbol'.

@
<symbol> ::= <symbol-or-alias>
@
-}
parseSymbolHead :: Parser Symbol
parseSymbolHead = parseSymbolOrAliasDeclarationHead Symbol

{-| Parses an pattern.

@
<pattern>
  ::= <element-variable>
    | <set-variable>
    | <ML-pattern>
    | <application-pattern>
    | <string-literal>
@
-}
parsePattern :: Parser ParsedPattern
parsePattern =
    (embedParsedPattern <$> parseLiteral) <|> (parseAnyId >>= parseRemainder)
  where
    parseRemainder identifier =
        (embedParsedPattern <$> parseVariableRemainder identifier)
        <|> parseKoreRemainder identifier
        <|> (embedParsedPattern <$> parseApplicationRemainder parsePattern identifier)

parseLiteral :: Parser (PatternF VariableName ParsedPattern)
parseLiteral =
    (StringLiteralF . Const <$> parseStringLiteral)
    <?> "string literal"

parseVariable :: Parser (SomeVariable VariableName)
parseVariable = do
    variableName <- parseAnyId >>= getSomeVariableName
    colon
    variableSort <- parseSort
    pure Variable { variableName, variableSort }

{- | Parse a variable, given that the identifier is already parsed.

@
<variable> ::= <element-variable> | <set-variable>
@

Set variables always start with @\@@, while element variables do not.
-}
parseVariableRemainder :: Id -> Parser (PatternF VariableName child)
parseVariableRemainder identifier = do
    variableName <- getSomeVariableName identifier
    colon
    variableSort <- parseSort
    (pure . VariableF . Const) Variable { variableName, variableSort }

getSomeVariableName :: Id -> Parser (SomeVariableName VariableName)
getSomeVariableName identifier =
    (inject <$> getSetVariableName identifier)
    <|> (inject <$> getElementVariableName identifier)

getSetVariableName :: Id -> Parser (SetVariableName VariableName)
getSetVariableName identifier
  | isSetVariableId identifier =
    pure (SetVariableName (getVariableName identifier))
  | otherwise = empty

{- | Parse a set variable.

@
<set-variable> ::= <set-variable-id> ":" <sort>
@
-}
parseSetVariable :: Parser (SetVariable VariableName)
parseSetVariable = do
    variableName <- parseSetId >>= getSetVariableName
    colon
    variableSort <- parseSort
    pure Variable { variableName, variableSort }

getElementVariableName :: Id -> Parser (ElementVariableName VariableName)
getElementVariableName identifier
  | isElementVariableId identifier =
    pure (ElementVariableName (getVariableName identifier))
  | otherwise = empty

{- | Parse an element variable.

@
<element-variable> ::= <element-variable-id> ":" <sort>
@
-}
parseElementVariable :: Parser (ElementVariable VariableName)
parseElementVariable = do
    variableName <- parseId >>= getElementVariableName
    colon
    variableSort <- parseSort
    pure Variable { variableName, variableSort }

parseSymbolOrAlias :: Parser SymbolOrAlias
parseSymbolOrAlias = parseSymbolId >>= parseSymbolOrAliasRemainder

parseApplication
    :: Parser child
    -> Parser (Application SymbolOrAlias child)
parseApplication parseChild = do
    applicationSymbolOrAlias <- parseSymbolOrAlias
    applicationChildren <- parseArguments parseChild
    pure Application { applicationSymbolOrAlias, applicationChildren }

parseApplicationRemainder
    :: Parser child
    -> Id
    -> Parser (PatternF VariableName child)
parseApplicationRemainder parseChild identifier = do
    applicationSymbolOrAlias <- parseSymbolOrAliasRemainder identifier
    applicationChildren <- parseArguments parseChild
    (pure . ApplicationF)
        Application { applicationSymbolOrAlias, applicationChildren }

parseLeftAssoc :: Parser ParsedPattern
parseLeftAssoc = do
    braces (pure ())
    application <- parens (parseApplication parsePattern)
    let mkApplication child1 child2 =
            application { applicationChildren = [child1, child2] }
            & ApplicationF
            & embedParsedPattern
    case applicationChildren application of
        [] -> fail "expected one or more arguments"
        children -> pure (foldl1 mkApplication children)

parseSymbolOrAliasRemainder :: Id -> Parser SymbolOrAlias
parseSymbolOrAliasRemainder symbolOrAliasConstructor = do
    Monad.guard (isSymbolId symbolOrAliasConstructor)
    symbolOrAliasParams <- parseParameters parseSort
    pure SymbolOrAlias { symbolOrAliasConstructor, symbolOrAliasParams }

{- | Parse a built-in Kore (matching logic) pattern.

@
<ML-pattern>
  ::=
    // Connectives
      "\top" "{" <sort> "}" "(" ")"
    | "\bottom" "{" <sort> "}" "(" ")"
    | "\not" "{" <sort> "}" "(" <pattern> ")"
    | "\and" "{" <sort> "}" "(" <pattern> "," <pattern> ")"
    | "\or" "{" <sort> "}" "(" <pattern> "," <pattern> ")"
    | "\implies" "{" <sort> "}" "(" <pattern> "," <pattern> ")"
    | "\iff" "{" <sort> "}" "(" <pattern> "," <pattern> ")"

    // Quantifiers
    | "\exists" "{" <sort> "}" "(" <element-variable> "," <pattern> ")"
    | "\forall" "{" <sort> "}" "(" <element-variable> "," <pattern> ")"

    // Fixpoints
    | "\mu" "(" <set-variable> "," <pattern> ")"
    | "\nu" "(" <set-variable> "," <pattern> ")"

    // Predicates
    | "\ceil" "{" <sort> "," <sort> "}" "(" <pattern> ")"
    | "\floor" "{" <sort> "," <sort> "}" "(" <pattern> ")"
    | "\equals" "{" <sort> "," <sort> "}" "(" <pattern> "," <pattern> ")"
    | "\in" "{" <sort> "," <sort> "}" "(" <pattern> "," <pattern> ")"

    // Rewriting
    | "\next" "{" <sort> "}" "(" <pattern> ")"
    | "\rewrites" "{" <sort> "}" "(" <pattern> "," <pattern> ")"

    // Values
    | "\dv" "{" <sort> "}" "(" <string-literal> ")"

    // Syntax sugar
    | "\left-assoc" "{" "}" "(" <application-pattern> ")"
@

Always starts with @\@.
-}
parseKoreRemainder :: Id -> Parser ParsedPattern
parseKoreRemainder identifier = do
    keyword <- getSpecialId identifier
    case keyword of
        -- Connectives
        "top" -> embedParsedPattern . TopF <$> parseConnective0 Top
        "bottom" -> embedParsedPattern . BottomF <$> parseConnective0 Bottom
        "not" -> embedParsedPattern . NotF <$> parseConnective1 Not
        "and" -> embedParsedPattern . AndF <$> parseConnective2 And
        "or" -> embedParsedPattern . OrF <$> parseConnective2 Or
        "implies" -> embedParsedPattern . ImpliesF <$> parseConnective2 Implies
        "iff" -> embedParsedPattern . IffF <$> parseConnective2 Iff
        -- Quantifiers
        "exists" -> embedParsedPattern . ExistsF <$> parseQuantifier Exists
        "forall" -> embedParsedPattern . ForallF <$> parseQuantifier Forall
        -- Fixpoints
        "mu" -> embedParsedPattern . MuF <$> parseFixpoint Mu
        "nu" -> embedParsedPattern . NuF <$> parseFixpoint Nu
        -- Predicates
        "ceil" -> embedParsedPattern . CeilF <$> parsePredicate1 Ceil
        "floor" -> embedParsedPattern . FloorF <$> parsePredicate1 Floor
        "equals" -> embedParsedPattern . EqualsF <$> parsePredicate2 Equals
        "in" -> embedParsedPattern . InF <$> parsePredicate2 In
        -- Rewriting
        "next" -> embedParsedPattern . NextF <$> parseConnective1 Next
        "rewrites" -> embedParsedPattern . RewritesF <$> parseConnective2 Rewrites
        -- Values
        "dv" -> embedParsedPattern . DomainValueF <$> parseDomainValue
        -- Syntax sugar
        "left-assoc" -> parseLeftAssoc

        _ -> empty

getSpecialId :: Id -> Parser Text
getSpecialId Id { getId } = do
    Monad.guard (Text.head getId == '\\')
    pure (Text.tail getId)

{- | Parse a 0-argument connective.

@
_ ::= _ "{" ⟨sort⟩ "}" "(" ")"
@
 -}
parseConnective0 :: (Sort -> result) -> Parser result
parseConnective0 mkResult =
    mkResult' <$> braces parseSort <*> parens (pure ())
  where
    mkResult' sort () = mkResult sort

{- | Parse a 1-argument connective.

@
_ ::= _ "{" ⟨sort⟩ "}" "(" ⟨pattern⟩ ")"
@
 -}
parseConnective1 :: (Sort -> ParsedPattern -> result) -> Parser result
parseConnective1 mkResult =
    mkResult <$> braces parseSort <*> parens parsePattern

{- | Parse a 2-argument connective.

@
_ ::= _ "{" ⟨sort⟩ "}" "(" ⟨pattern⟩ "," ⟨pattern⟩ ")"
@
 -}
parseConnective2
    :: (Sort -> ParsedPattern -> ParsedPattern -> result)
    -> Parser result
parseConnective2 mkResult =
    mkResult' <$> braces parseSort <*> parensPair parsePattern
  where
    mkResult' sort (child1, child2) = mkResult sort child1 child2

{- | Parse a quantifier.

@
_ ::= _ "{" ⟨sort⟩ "}" "(" ⟨element-variable⟩ "," ⟨pattern⟩ ")"
@
 -}
parseQuantifier
    :: (Sort -> ElementVariable VariableName -> ParsedPattern -> result)
    -> Parser result
parseQuantifier mkResult =
    mkResult'
        <$> braces parseSort
        <*> parensTuple parseElementVariable parsePattern
  where
    mkResult' sort (variable, child) = mkResult sort variable child

{- | Parse a fixpoint.

@
_ ::= _ "{" ⟨sort⟩ "}" "(" ⟨set-variable⟩ "," ⟨pattern⟩ ")"
@
 -}
parseFixpoint
    :: (SetVariable VariableName -> ParsedPattern -> result)
    -> Parser result
parseFixpoint mkResult =
    mkResult'
        <$> braces (pure ())
        <*> parensTuple parseSetVariable parsePattern
  where
    mkResult' () (variable, child) = mkResult variable child

{- | Parse a 1-argument predicate.

@
_ ::= _ "{" ⟨sort⟩ "," ⟨sort⟩ "}" "(" ⟨pattern⟩ ")"
@
 -}
parsePredicate1
    :: (Sort -> Sort -> ParsedPattern -> result)
    -> Parser result
parsePredicate1 mkResult =
    mkResult' <$> bracesPair parseSort <*> parens parsePattern
  where
    mkResult' (sort1, sort2) child = mkResult sort1 sort2 child

{- | Parse a 2-argument predicate.

@
_ ::= _ "{" ⟨sort⟩ "," ⟨sort⟩ "}" "(" ⟨pattern⟩ "," ⟨pattern⟩ ")"
@
 -}
parsePredicate2
    :: (Sort -> Sort -> ParsedPattern -> ParsedPattern -> result)
    -> Parser result
parsePredicate2 mkResult =
    mkResult' <$> bracesPair parseSort <*> parensPair parsePattern
  where
    mkResult' (sort1, sort2) (child1, child2) =
        mkResult sort1 sort2 child1 child2

getVariableName :: Id -> VariableName
getVariableName identifier =
    let (base, counter) = parseVariableCounter identifier
    in VariableName { base, counter }

parseVariableCounter :: Id -> (Id, Maybe (Sup Natural))
parseVariableCounter identifier@Id { getId, idLocation }
  -- Cases:
  -- suffix is empty: no counter, Id is not changed
  | Text.null suffix = (identifier, Nothing)
  -- suffix is all zeros: counter is zero, Id has final zero stripped
  | Text.null nonZeros =
    ( Id { idLocation, getId = base <> Text.init zeros }
    , Just (Element 0)
    )
  -- suffix is some zeros followed by non-zeros:
  --   read the counter from the non-zeros, Id is base + zeros
  | otherwise =
    ( Id { idLocation, getId = base <> zeros }
    , (Just . Element) (read $ Text.unpack nonZeros)
    )
  where
    base = Text.dropWhileEnd Char.isDigit getId
    suffix = Text.drop (Text.length base) getId
    zeros = Text.takeWhile (== '0') suffix
    nonZeros = Text.drop (Text.length zeros) suffix

parseDomainValue :: Parser (DomainValue Sort ParsedPattern)
parseDomainValue =
    DomainValue <$> braces parseSort <*> parens parseChild
  where
    parseChild =
        embedParsedPattern . StringLiteralF . Const <$> parseStringLiteral

{-|'inParenthesesListParser' is the same as 'inSquareBracketsListParser'
except that it uses parentheses instead of square brackets.
-}
parseArguments :: Parser item -> Parser [item]
parseArguments parseItem = parens (Parse.sepBy parseItem comma)

{- | Parse a list of parameters to a term head or sort.

Parameter lists are comma-separated and surrounded by braces.

-}
parseParameters :: Parser item -> Parser [item]
parseParameters parseItem =
    Parse.between lbrace rbrace (Parse.sepBy parseItem comma)

{-| Parser a (possibly empty) comma separated list of attributes enclosed in
square brackets.

BNF definition:

@
⟨attributes⟩ ::= ‘[’ ⟨patterns⟩ ‘]’
@

Always starts with @[@.
-}
attributesParser :: Parser Attributes
attributesParser =
    Attributes <$> brackets (Parse.sepBy parsePattern comma)

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
    aliasSymbol <- parseSymbolHead
    sorts <- parseArguments parseSort
    colonParser
    resultSort <- parseSort
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
    aliasSymbol <- parseAliasHead
    sorts <- parseArguments parseSort
    colonParser
    resultSort <- parseSort
    mlLexemeParser "where"
    -- Note: constraints for left pattern checked in verifySentence
    leftPattern <- parseApplication parseVariable
    mlLexemeParser ":="
    rightPattern <- parsePattern
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
            <$> parseParameters parseSortVariable
            <*> parsePattern
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
            <$> parseSortId
            <*> parseParameters parseSortVariable
            <*> attributesParser
        )
