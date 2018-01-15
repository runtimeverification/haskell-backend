module KoreParserImpl where

import           KoreAST
import           KoreLexeme

import           Control.Applicative              ((<|>))
import           Control.Monad                    (void)

import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser

objectSortVariableParser :: Parser ObjectSortVariable
objectSortVariableParser = ObjectSortVariable <$> idParser

metaSortVariableParser :: Parser MetaSortVariable
metaSortVariableParser = MetaSortVariable <$> metaIdParser

sortVariableParser :: Parser SortVariable
sortVariableParser = do
    c <- Parser.peekChar'
    if c == '#'
        then MetaSortVariableSortVariable <$> metaSortVariableParser
        else ObjectSortVariableSortVariable <$> objectSortVariableParser

sortVariableListParser :: Parser [SortVariable]
sortVariableListParser = Parser.sepBy sortVariableParser commaParser

objectSortParser :: Parser ObjectSort
objectSortParser = do
    identifier <- idParser
    actualSortParser identifier <|>
        return (ObjectSortVariableSort $ ObjectSortVariable identifier)
  where
    actualSortParser identifier = do
        sorts <- inCurlyBracesParser objectSortListParser
        return ActualSort
            { actualSortName = identifier
            , actualSortSorts = sorts
            }

metaSortParser :: Parser MetaSort
metaSortParser = do
    identifier <- metaIdParser
    mc <- Parser.peekChar
    case mc of
        Just '{' ->
            inCurlyBracesParser (return ()) *> concreteMetaSort identifier
        _        ->
            return (MetaSortVariableMetaSort $ MetaSortVariable $ identifier)
  where
    concreteMetaSort (MetaId metaId) = case metaId of
        "#Char" -> return CharMetaSort
        "#CharList" -> return CharListMetaSort
        "#Pattern" -> return PatternMetaSort
        "#PatternList" -> return PatternListMetaSort
        "#ObjectSort" -> return SortMetaSort
        "#SortList" -> return SortListMetaSort
        "#String" -> return StringMetaSort
        "#ObjectSymbol" -> return SymbolMetaSort
        "#SymbolList" -> return SymbolListMetaSort
        "#Variable" -> return VariableMetaSort
        "#VariableList" -> return VariableListMetaSort
        str -> fail ("metaSortParser: Invalid constructor: '" ++ str ++ "'.")

objectSortListParser :: Parser [ObjectSort]
objectSortListParser = Parser.sepBy objectSortParser commaParser

metaSortListParser :: Parser [MetaSort]
metaSortListParser = Parser.sepBy metaSortParser commaParser

objectSymbolOrAliasRemainderRawParser :: ([ObjectSort] -> a) -> Parser a
objectSymbolOrAliasRemainderRawParser constructor =
    constructor <$> inCurlyBracesParser objectSortListParser

objectSymbolOrAliasRawParser :: (Id -> [ObjectSort] -> a) -> Parser a
objectSymbolOrAliasRawParser constructor = do
    headConstructor <- idParser
    objectSymbolOrAliasRemainderRawParser (constructor headConstructor)

metaSymbolOrAliasRemainderRawParser :: ([MetaSort] -> a) -> Parser a
metaSymbolOrAliasRemainderRawParser constructor =
    constructor <$> inCurlyBracesParser metaSortListParser

metaSymbolOrAliasRawParser :: (MetaId -> [MetaSort] -> a) -> Parser a
metaSymbolOrAliasRawParser constructor = do
    headConstructor <- metaIdParser
    metaSymbolOrAliasRemainderRawParser (constructor headConstructor)

objectAliasParser :: Parser ObjectAlias
objectAliasParser = objectSymbolOrAliasRawParser ObjectAlias

objectSymbolParser :: Parser ObjectSymbol
objectSymbolParser = objectSymbolOrAliasRawParser ObjectSymbol

objectSymbolOrAliasRemainderParser :: Id -> Parser ObjectSymbolOrAlias
objectSymbolOrAliasRemainderParser identifier =
    objectSymbolOrAliasRemainderRawParser (ObjectSymbolOrAlias identifier)

metaAliasParser :: Parser MetaAlias
metaAliasParser = metaSymbolOrAliasRawParser MetaAlias

metaSymbolParser :: Parser MetaSymbol
metaSymbolParser = metaSymbolOrAliasRawParser MetaSymbol

metaSymbolOrAliasRemainderParser :: MetaId -> Parser MetaSymbolOrAlias
metaSymbolOrAliasRemainderParser identifier =
    metaSymbolOrAliasRemainderRawParser (MetaSymbolOrAlias identifier)

unaryOperatorRemainderParser :: (ObjectSort -> Pattern -> Pattern) ->  Parser Pattern
unaryOperatorRemainderParser constructor =
    pure constructor
        <*> inCurlyBracesParser objectSortParser
        <*> inParenthesesParser patternParser

binaryOperatorRemainderParser
    :: (ObjectSort -> Pattern -> Pattern -> Pattern)
    -> Parser Pattern
binaryOperatorRemainderParser constructor = do
    sort <- inCurlyBracesParser objectSortParser
    (pattern1, pattern2) <- parenPairParser patternParser patternParser
    return (constructor sort pattern1 pattern2)

existsForallRemainderParser
    :: (ObjectSort -> Variable -> Pattern -> Pattern)
    -> Parser Pattern
existsForallRemainderParser constructor = do
    sort <- inCurlyBracesParser objectSortParser
    (variable, pattern) <- parenPairParser variableParser patternParser
    return (constructor sort variable pattern)

ceilFloorRemainderParser
    :: (ObjectSort -> ObjectSort -> Pattern -> Pattern)
    -> Parser Pattern
ceilFloorRemainderParser constructor = do
    (sort1, sort2) <- curlyPairParser objectSortParser objectSortParser
    pattern <- inParenthesesParser patternParser
    return (constructor sort1 sort2 pattern)

memRemainderParser :: Parser Pattern
memRemainderParser = do
    (sort1, sort2) <- curlyPairParser objectSortParser objectSortParser
    (variable, pattern) <- parenPairParser variableParser patternParser
    return MemPattern
           { memPatternFirstSort = sort1
           , memPatternSecondSort = sort2
           , memPatternVariable = variable
           , memPatternPattern = pattern
           }

equalsLikeRemainderParser
    :: (ObjectSort -> ObjectSort -> Pattern -> Pattern -> Pattern)
    -> Parser Pattern
equalsLikeRemainderParser constructor = do
    (sort1, sort2) <- curlyPairParser objectSortParser objectSortParser
    (pattern1, pattern2) <- parenPairParser patternParser patternParser
    return (constructor sort1 sort2 pattern1 pattern2)

topBottomRemainderParser :: (ObjectSort -> Pattern) -> Parser Pattern
topBottomRemainderParser constructor = do
    sort <- inCurlyBracesParser objectSortParser
    inParenthesesParser (return ())
    return (constructor sort)

symbolOrAliasPatternRemainderParser :: Id -> Parser Pattern
symbolOrAliasPatternRemainderParser identifier =
    pure ApplicationPattern
        <*> objectSymbolOrAliasRemainderParser identifier
        <*> inParenthesesParser patternListParser

variableRemainderParser :: Id -> Parser Variable
variableRemainderParser identifier = do
    colonParser
    sort <- objectSortParser
    return Variable
        { variableName = identifier
        , variableSort = sort
        }

variableParser :: Parser Variable
variableParser = idParser >>= variableRemainderParser

variableOrTermPatternParser :: Parser Pattern
variableOrTermPatternParser = do
    identifier <- idParser
    c <- Parser.peekChar'
    if c == ':'
        then VariablePattern <$> variableRemainderParser identifier
        else symbolOrAliasPatternRemainderParser identifier

mlConstructorParser :: Parser Pattern
mlConstructorParser = do
    void (Parser.char '\\')
    mlPatternParser
  where
    mlPatternParser = keywordBasedParsers
        [ ("and", binaryOperatorRemainderParser AndPattern)
        , ("bottom", topBottomRemainderParser BottomPattern)
        , ("ceil", ceilFloorRemainderParser CeilPattern)
        , ("equals", equalsLikeRemainderParser EqualsPattern)
        , ("exists", existsForallRemainderParser ExistsPattern)
        , ("floor", ceilFloorRemainderParser FloorPattern)
        , ("forall", existsForallRemainderParser ForallPattern)
        , ("iff", binaryOperatorRemainderParser IffPattern)
        , ("implies", binaryOperatorRemainderParser ImpliesPattern)
        , ("mem", memRemainderParser)
        , ("not", unaryOperatorRemainderParser NotPattern)
        , ("or", binaryOperatorRemainderParser OrPattern)
        , ("top", topBottomRemainderParser TopPattern)
        ]

patternParser :: Parser Pattern
patternParser = do
    c <- Parser.peekChar'
    case c of
        '\\' -> mlConstructorParser
        '"'  -> StringLiteralPattern <$> stringLiteralParser
        _    -> variableOrTermPatternParser

patternListParser :: Parser [Pattern]
patternListParser = Parser.sepBy patternParser commaParser

attributesParser :: Parser Attributes
attributesParser =
    Attributes <$> inSquareBracketsParser patternListParser

definitionParser :: Parser Definition
definitionParser =
    pure Definition
        <*> attributesParser
        <*> moduleParser

moduleParser :: Parser Module
moduleParser = do
    mlLexemeParser "module"
    name <- moduleNameParser
    sentences <- Parser.many1 sentenceParser
    mlLexemeParser "endmodule"
    attributes <- attributesParser
    return Module
           { moduleName = name
           , moduleSentences = sentences
           , moduleAttributes = attributes
           }

sentenceParser :: Parser Sentence
sentenceParser = keywordBasedParsers
    [ ( "alias"
      , aliasSymbolSentenceRemainderParser objectAliasParser AliasSentence
      )
    , ( "axiom", axiomSentenceRemainderParser )
    , ( "sort", sortSentenceRemainderParser )
    , ( "symbol"
      , aliasSymbolSentenceRemainderParser objectSymbolParser SymbolSentence)
    ]

aliasSymbolSentenceRemainderParser
    :: Parser a
    -> (a -> [ObjectSort] -> ObjectSort -> Attributes -> Sentence)
    -> Parser Sentence
aliasSymbolSentenceRemainderParser aliasSymbolParser constructor = do
    aliasSymbol <- aliasSymbolParser
    sorts <- inParenthesesParser objectSortListParser
    colonParser
    resultSort <- objectSortParser
    attributes <- attributesParser
    return (constructor aliasSymbol sorts resultSort attributes)

axiomSentenceRemainderParser :: Parser Sentence
axiomSentenceRemainderParser =
    pure AxiomSentence
        <*> inCurlyBracesParser sortVariableListParser
        <*> patternParser
        <*> attributesParser

sortSentenceRemainderParser :: Parser Sentence
sortSentenceRemainderParser =
    pure SortSentence
        <*> inCurlyBracesParser sortVariableListParser
        <*> objectSortParser
        <*> attributesParser
