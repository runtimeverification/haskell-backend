module KoreParser where

import           KoreAST
import           KoreLexeme

import           Control.Applicative
import           Control.Monad

import qualified Data.Attoparsec.ByteString.Char8 as Parser

sortParser :: Parser.Parser Sort
sortParser = do
    identifier <- idParser
    actualSortParser identifier <|>
        return (SortVariableSort $ SortVariable identifier)
  where
    actualSortParser identifier = do
        openCurlyBraceParser
        sorts <- sortListParser
        closedCurlyBraceParser
        return ActualSort
            { actualSortName = identifier
            , actualSortSorts = sorts
            }

sortListParser :: Parser.Parser [Sort]
sortListParser = Parser.sepBy sortParser commaParser

symbolOrAliasRemainderRawParser :: ([Sort] -> a) -> Parser.Parser a
symbolOrAliasRemainderRawParser constructor = do
    openCurlyBraceParser
    sorts <- sortListParser
    closedCurlyBraceParser
    return (constructor sorts)

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
notRemainderParser = do
    openCurlyBraceParser
    sort <- sortParser
    closedCurlyBraceParser
    openParenthesisParser
    pattern <- patternParser
    closedParenthesisParser
    return NotPattern
        { notPatternSort = sort
        , notPatternPattern = pattern
        }

binaryOperatorRemainderParser
    :: (Sort -> Pattern -> Pattern -> Pattern)
    -> Parser.Parser Pattern
binaryOperatorRemainderParser constructor = do
    openCurlyBraceParser
    sort <- sortParser
    closedCurlyBraceParser
    openParenthesisParser
    pattern1 <- patternParser
    commaParser
    pattern2 <- patternParser
    closedParenthesisParser
    return (constructor sort pattern1 pattern2)

existsForallRemainderParser
    :: (Sort -> Variable -> Pattern -> Pattern)
    -> Parser.Parser Pattern
existsForallRemainderParser constructor = do
    openCurlyBraceParser
    sort <- sortParser
    closedCurlyBraceParser
    openParenthesisParser
    variable <- variableParser
    commaParser
    pattern <- patternParser
    closedParenthesisParser
    return (constructor sort variable pattern)

ceilFloorRemainderParser
    :: (Sort -> Sort -> Pattern -> Pattern)
    -> Parser.Parser Pattern
ceilFloorRemainderParser constructor = do
    openCurlyBraceParser
    sort1 <- sortParser
    commaParser
    sort2 <- sortParser
    closedCurlyBraceParser
    openParenthesisParser
    pattern <- patternParser
    closedParenthesisParser
    return (constructor sort1 sort2 pattern)

memRemainderParser :: Parser.Parser Pattern
memRemainderParser = do
    openCurlyBraceParser
    sort1 <- sortParser
    commaParser
    sort2 <- sortParser
    closedCurlyBraceParser
    openParenthesisParser
    variable <- variableParser
    commaParser
    pattern <- patternParser
    closedParenthesisParser
    return MemPattern
           { memPatternFirstSort = sort1
           , memPatternSecondSort = sort2
           , memPatternVariable = variable
           , memPatternPattern = pattern
           }

equalsRemainderParser :: Parser.Parser Pattern
equalsRemainderParser = do
    openCurlyBraceParser
    sort1 <- sortParser
    commaParser
    sort2 <- sortParser
    closedCurlyBraceParser
    openParenthesisParser
    pattern1 <- patternParser
    commaParser
    pattern2 <- patternParser
    closedParenthesisParser
    return EqualsPattern
           { equalsPatternFirstSort = sort1
           , equalsPatternSecondSort = sort2
           , equalsPatternFirst = pattern1
           , equalsPatternSecond = pattern2
           }

topBottomRemainderParser :: (Sort -> Pattern) -> Parser.Parser Pattern
topBottomRemainderParser constructor = do
    openCurlyBraceParser
    sort <- sortParser
    closedCurlyBraceParser
    return (constructor sort)

symbolOrAliasPatternRemainderParser :: Id -> Parser.Parser Pattern
symbolOrAliasPatternRemainderParser identifier = do
    symbolOrAlias <- symbolOrAliasRemainderParser identifier
    openParenthesisParser
    patterns <- patternListParser
    closedParenthesisParser
    return ApplicationPattern
        { applicationPatternSymbolOrAlias = symbolOrAlias
        , applicationPatternPatterns = patterns
        }

variablePatternRemainderParser :: Id -> Parser.Parser Pattern
variablePatternRemainderParser identifier = do
    colonParser
    sort <- sortParser
    return (VariablePattern Variable
        { variableName = identifier
        , variableSort = sort
        })

variableParser :: Parser.Parser Variable
variableParser = do
    identifier <- idParser
    getVariablePattern <$> variablePatternRemainderParser identifier

variableOrTermPatternParser :: Parser.Parser Pattern
variableOrTermPatternParser = do
    identifier <- idParser
    c <- Parser.peekChar'
    if c == ':'
        then variablePatternRemainderParser identifier
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
        , ("floor", existsForallRemainderParser ForallPattern)
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
attributesParser = do
    openSquareBracketParser
    patterns <- patternListParser
    closedSquareBracketParser
    return (Attributes patterns)

definitionParser :: Parser.Parser Definition
definitionParser = do
    attributes <- attributesParser
    modules <- Parser.many1 moduleParser
    return Definition
      { definitionAttributes = attributes
      , definitionModules = modules
      }

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
    [ ("alias", aliasSentenceRemainderParser)
    , ("axiom", axiomSentenceRemainderParser)
    , ("import", importSentenceRemainderParser)
    , ("sort", sortSentenceRemainderParser)
    , ("symbol", symbolSentenceRemainderParser)
    ]

aliasSentenceRemainderParser = undefined
axiomSentenceRemainderParser = undefined
importSentenceRemainderParser = undefined
sortSentenceRemainderParser = undefined
symbolSentenceRemainderParser = undefined