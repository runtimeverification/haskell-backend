module KoreParserImpl where

import           KoreAST
import           KoreLexeme

import           Control.Applicative ((<|>))
import           Control.Monad (void)

import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser

sortVariableParser :: Parser SortVariable
sortVariableParser = SortVariable <$> idParser

sortVariableList1Parser :: Parser [SortVariable]
sortVariableList1Parser = Parser.sepBy1 sortVariableParser commaParser

sortParser :: Parser Sort
sortParser = do
    identifier <- idParser
    actualSortParser identifier <|>
        return (SortVariableSort $ SortVariable identifier)
  where
    actualSortParser identifier = do
        sorts <- inCurlyBracesParser sortListParser
        return ActualSort
            { actualSortName = identifier
            , actualSortSorts = sorts
            }

sortListParser :: Parser [Sort]
sortListParser = Parser.sepBy sortParser commaParser

symbolOrAliasRemainderRawParser :: ([Sort] -> a) -> Parser a
symbolOrAliasRemainderRawParser constructor =
    constructor <$> inCurlyBracesParser sortListParser

symbolOrAliasRawParser :: (Id -> [Sort] -> a) -> Parser a
symbolOrAliasRawParser constructor = do
    headConstructor <- idParser
    symbolOrAliasRemainderRawParser (constructor headConstructor)

aliasParser :: Parser Alias
aliasParser = symbolOrAliasRawParser Alias

symbolParser :: Parser Symbol
symbolParser = symbolOrAliasRawParser Symbol

symbolOrAliasRemainderParser :: Id -> Parser SymbolOrAlias
symbolOrAliasRemainderParser identifier =
    symbolOrAliasRemainderRawParser (SymbolOrAlias identifier)

unaryOperatorRemainderParser :: (Sort -> Pattern -> Pattern) ->  Parser Pattern
unaryOperatorRemainderParser constructor =
    pure constructor
        <*> inCurlyBracesParser sortParser
        <*> inParenthesesParser patternParser

binaryOperatorRemainderParser
    :: (Sort -> Pattern -> Pattern -> Pattern)
    -> Parser Pattern
binaryOperatorRemainderParser constructor = do
    sort <- inCurlyBracesParser sortParser
    (pattern1, pattern2) <- parenPairParser patternParser patternParser
    return (constructor sort pattern1 pattern2)

existsForallRemainderParser
    :: (Sort -> Variable -> Pattern -> Pattern)
    -> Parser Pattern
existsForallRemainderParser constructor = do
    sort <- inCurlyBracesParser sortParser
    (variable, pattern) <- parenPairParser variableParser patternParser
    return (constructor sort variable pattern)

ceilFloorRemainderParser
    :: (Sort -> Sort -> Pattern -> Pattern)
    -> Parser Pattern
ceilFloorRemainderParser constructor = do
    (sort1, sort2) <- curlyPairParser sortParser sortParser
    pattern <- inParenthesesParser patternParser
    return (constructor sort1 sort2 pattern)

memRemainderParser :: Parser Pattern
memRemainderParser = do
    (sort1, sort2) <- curlyPairParser sortParser sortParser
    (variable, pattern) <- parenPairParser variableParser patternParser
    return MemPattern
           { memPatternFirstSort = sort1
           , memPatternSecondSort = sort2
           , memPatternVariable = variable
           , memPatternPattern = pattern
           }

equalsLikeRemainderParser
    :: (Sort -> Sort -> Pattern -> Pattern -> Pattern)
    -> Parser Pattern
equalsLikeRemainderParser constructor = do
    (sort1, sort2) <- curlyPairParser sortParser sortParser
    (pattern1, pattern2) <- parenPairParser patternParser patternParser
    return (constructor sort1 sort2 pattern1 pattern2)

topBottomRemainderParser :: (Sort -> Pattern) -> Parser Pattern
topBottomRemainderParser constructor = do
    sort <- inCurlyBracesParser sortParser
    inParenthesesParser (return ())
    return (constructor sort)

symbolOrAliasPatternRemainderParser :: Id -> Parser Pattern
symbolOrAliasPatternRemainderParser identifier =
    pure ApplicationPattern
        <*> symbolOrAliasRemainderParser identifier
        <*> inParenthesesParser patternListParser

variableRemainderParser :: Id -> Parser Variable
variableRemainderParser identifier = do
    colonParser
    sort <- sortParser
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

domainValueRemainderParser :: Parser Pattern
domainValueRemainderParser = do
    (string1, string2) <- parenPairParser stringLiteralParser stringLiteralParser
    return DomainValuePattern
        { domainValuePatternFirst = string1
        , domainValuePatternSecond = string2
        }

mlConstructorParser :: Parser Pattern
mlConstructorParser = do
    void (Parser.char '\\')
    mlPatternParser
  where
    mlPatternParser = keywordBasedParsers
        [ ("and", binaryOperatorRemainderParser AndPattern)
        , ("bottom", topBottomRemainderParser BottomPattern)
        , ("ceil", ceilFloorRemainderParser CeilPattern)
        , ("domainValue", domainValueRemainderParser)
        , ("equals", equalsLikeRemainderParser EqualsPattern)
        , ("exists", existsForallRemainderParser ExistsPattern)
        , ("floor", ceilFloorRemainderParser FloorPattern)
        , ("forall", existsForallRemainderParser ForallPattern)
        , ("iff", binaryOperatorRemainderParser IffPattern)
        , ("implies", binaryOperatorRemainderParser ImpliesPattern)
        , ("mem", memRemainderParser)
        , ("next", unaryOperatorRemainderParser NextPattern)
        , ("not", unaryOperatorRemainderParser NotPattern)
        , ("or", binaryOperatorRemainderParser OrPattern)
        , ("rewrites", equalsLikeRemainderParser RewritesPattern)
        , ("subset", equalsLikeRemainderParser SubsetPattern)
        , ("top", topBottomRemainderParser TopPattern)
        ]

patternParser :: Parser Pattern
patternParser = do
    c <- Parser.peekChar'
    case c of
        '\\' -> mlConstructorParser
        '"' -> StringLiteralPattern <$> stringLiteralParser
        _ -> variableOrTermPatternParser

patternListParser :: Parser [Pattern]
patternListParser = Parser.sepBy patternParser commaParser

attributesParser :: Parser Attributes
attributesParser =
    Attributes <$> inSquareBracketsParser patternListParser

definitionParser :: Parser Definition
definitionParser =
    pure Definition
        <*> attributesParser
        <*> Parser.many1 moduleParser

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
    [ ("alias", aliasSymbolSentenceRemainderParser aliasParser AliasSentence)
    , ("axiom", axiomSentenceRemainderParser)
    , ("import", importSentenceRemainderParser)
    , ("sort", sortSentenceRemainderParser)
    , ("symbol", aliasSymbolSentenceRemainderParser symbolParser SymbolSentence)
    ]

aliasSymbolSentenceRemainderParser
    :: Parser a
    -> (a -> [Sort] -> Sort -> Attributes -> Sentence)
    -> Parser Sentence
aliasSymbolSentenceRemainderParser aliasSymbolParser constructor = do
    aliasSymbol <- aliasSymbolParser
    sorts <- inParenthesesParser sortListParser
    colonParser
    resultSort <- sortParser
    attributes <- attributesParser
    return (constructor aliasSymbol sorts resultSort attributes)

axiomSentenceRemainderParser :: Parser Sentence
axiomSentenceRemainderParser =
    pure AxiomSentence
        <*> inCurlyBracesParser sortVariableList1Parser
        <*> patternParser
        <*> attributesParser

importSentenceRemainderParser :: Parser Sentence
importSentenceRemainderParser =
    pure ImportSentence
        <*> moduleNameParser
        <*> attributesParser

sortSentenceRemainderParser :: Parser Sentence
sortSentenceRemainderParser =
    pure SortSentence
        <*> inCurlyBracesParser sortVariableList1Parser
        <*> sortParser
        <*> attributesParser
