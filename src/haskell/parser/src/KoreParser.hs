module KoreParser where

import           KoreAST
import           KoreLexeme

import           Control.Applicative

import qualified Data.Attoparsec.ByteString.Char8 as Parser

sortVariableParser :: Parser.Parser SortVariable
sortVariableParser = SortVariable <$> idParser

sortVariableList1Parser :: Parser.Parser [SortVariable]
sortVariableList1Parser = Parser.sepBy1 sortVariableParser commaParser

sortParser :: Parser.Parser Sort
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

sortListParser :: Parser.Parser [Sort]
sortListParser = Parser.sepBy sortParser commaParser

symbolOrAliasRemainderRawParser :: ([Sort] -> a) -> Parser.Parser a
symbolOrAliasRemainderRawParser constructor =
    constructor <$> inCurlyBracesParser sortListParser

symbolOrAliasRawParser :: (Id -> [Sort] -> a) -> Parser.Parser a
symbolOrAliasRawParser constructor = do
    headConstructor <- idParser
    symbolOrAliasRemainderRawParser (constructor headConstructor)

aliasParser :: Parser.Parser Alias
aliasParser = symbolOrAliasRawParser Alias

symbolParser :: Parser.Parser Symbol
symbolParser = symbolOrAliasRawParser Symbol

symbolOrAliasRemainderParser :: Id -> Parser.Parser SymbolOrAlias
symbolOrAliasRemainderParser identifier =
    symbolOrAliasRemainderRawParser (SymbolOrAlias identifier)

notRemainderParser :: Parser.Parser Pattern
notRemainderParser =
    pure NotPattern
        <*> inCurlyBracesParser sortParser
        <*> inParenthesesParser patternParser

binaryOperatorRemainderParser
    :: (Sort -> Pattern -> Pattern -> Pattern)
    -> Parser.Parser Pattern
binaryOperatorRemainderParser constructor = do
    sort <- inCurlyBracesParser sortParser
    (pattern1, pattern2) <- parenPairParser patternParser patternParser
    return (constructor sort pattern1 pattern2)

existsForallRemainderParser
    :: (Sort -> Variable -> Pattern -> Pattern)
    -> Parser.Parser Pattern
existsForallRemainderParser constructor = do
    sort <- inCurlyBracesParser sortParser
    (variable, pattern) <- parenPairParser variableParser patternParser
    return (constructor sort variable pattern)

ceilFloorRemainderParser
    :: (Sort -> Sort -> Pattern -> Pattern)
    -> Parser.Parser Pattern
ceilFloorRemainderParser constructor = do
    (sort1, sort2) <- curlyPairParser sortParser sortParser
    pattern <- inParenthesesParser patternParser
    return (constructor sort1 sort2 pattern)

memRemainderParser :: Parser.Parser Pattern
memRemainderParser = do
    (sort1, sort2) <- curlyPairParser sortParser sortParser
    (variable, pattern) <- parenPairParser variableParser patternParser
    return MemPattern
           { memPatternFirstSort = sort1
           , memPatternSecondSort = sort2
           , memPatternVariable = variable
           , memPatternPattern = pattern
           }

equalsRemainderParser :: Parser.Parser Pattern
equalsRemainderParser = do
    (sort1, sort2) <- curlyPairParser sortParser sortParser
    (pattern1, pattern2) <- parenPairParser patternParser patternParser
    return EqualsPattern
           { equalsPatternFirstSort = sort1
           , equalsPatternSecondSort = sort2
           , equalsPatternFirst = pattern1
           , equalsPatternSecond = pattern2
           }

topBottomRemainderParser :: (Sort -> Pattern) -> Parser.Parser Pattern
topBottomRemainderParser constructor = do
    sort <- inCurlyBracesParser sortParser
    inParenthesesParser (return ())
    return (constructor sort)

symbolOrAliasPatternRemainderParser :: Id -> Parser.Parser Pattern
symbolOrAliasPatternRemainderParser identifier =
    pure ApplicationPattern
        <*> symbolOrAliasRemainderParser identifier
        <*> inParenthesesParser patternListParser

variableRemainderParser :: Id -> Parser.Parser Variable
variableRemainderParser identifier = do
    colonParser
    sort <- sortParser
    return Variable
        { variableName = identifier
        , variableSort = sort
        }

variableParser :: Parser.Parser Variable
variableParser = idParser >>= variableRemainderParser

variableOrTermPatternParser :: Parser.Parser Pattern
variableOrTermPatternParser = do
    identifier <- idParser
    c <- Parser.peekChar'
    if c == ':'
        then VariablePattern <$> variableRemainderParser identifier
        else symbolOrAliasPatternRemainderParser identifier

mlConstructorParser :: Parser.Parser Pattern
mlConstructorParser = do
    Parser.char '\\'
    mlPatternParser
  where
    mlPatternParser = keywordBasedParsers
        [ ("and", binaryOperatorRemainderParser AndPattern)
        , ("bottom", topBottomRemainderParser BottomPattern)
        , ("ceil", ceilFloorRemainderParser CeilPattern)
        , ("equals", equalsRemainderParser)
        , ("exists", existsForallRemainderParser ExistsPattern)
        , ("floor", ceilFloorRemainderParser FloorPattern)
        , ("forall", existsForallRemainderParser ForallPattern)
        , ("iff", binaryOperatorRemainderParser IffPattern)
        , ("implies", binaryOperatorRemainderParser ImpliesPattern)
        , ("mem", memRemainderParser)
        , ("not", notRemainderParser)
        , ("or", binaryOperatorRemainderParser OrPattern)
        , ("top", topBottomRemainderParser TopPattern)
        ]
{-TODO?
2,3 next
2,3 rewrites
2,3 subset
2 domainValue
-}

patternParser :: Parser.Parser Pattern
patternParser = do
    c <- Parser.peekChar'
    case c of
        '\\' -> mlConstructorParser
        '"' -> StringLiteralPattern <$> stringLiteralParser
        _ -> variableOrTermPatternParser

patternListParser :: Parser.Parser [Pattern]
patternListParser = Parser.sepBy patternParser commaParser

attributesParser :: Parser.Parser Attributes
attributesParser =
    Attributes <$> inSquareBracketsParser patternListParser

definitionParser :: Parser.Parser Definition
definitionParser =
    pure Definition
        <*> attributesParser
        <*> Parser.many1 moduleParser

moduleParser :: Parser.Parser Module
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

sentenceParser :: Parser.Parser Sentence
sentenceParser = keywordBasedParsers
    [ ("alias", aliasSymbolSentenceRemainderParser aliasParser AliasSentence)
    , ("axiom", axiomSentenceRemainderParser)
    , ("import", importSentenceRemainderParser)
    , ("sort", sortSentenceRemainderParser)
    , ("symbol", aliasSymbolSentenceRemainderParser symbolParser SymbolSentence)
    ]

aliasSymbolSentenceRemainderParser
    :: Parser.Parser a
    -> (a -> [Sort] -> Sort -> Attributes -> Sentence)
    -> Parser.Parser Sentence
aliasSymbolSentenceRemainderParser aliasSymbolParser constructor = do
    aliasSymbol <- aliasSymbolParser
    sorts <- inParenthesesParser sortListParser
    colonParser
    resultSort <- sortParser
    attributes <- attributesParser
    return (constructor aliasSymbol sorts resultSort attributes)

axiomSentenceRemainderParser :: Parser.Parser Sentence
axiomSentenceRemainderParser =
    pure AxiomSentence
        <*> inCurlyBracesParser sortVariableList1Parser
        <*> patternParser
        <*> attributesParser

importSentenceRemainderParser :: Parser.Parser Sentence
importSentenceRemainderParser =
    ImportSentence <$> moduleNameParser <*> attributesParser

sortSentenceRemainderParser :: Parser.Parser Sentence
sortSentenceRemainderParser =
    pure SortSentence
        <*> inCurlyBracesParser sortVariableList1Parser
        <*> sortParser
        <*> attributesParser
