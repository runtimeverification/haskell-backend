module KoreParser where

import           KoreAST
import           KoreLexeme

import           Control.Applicative
import           Control.Monad

import qualified Data.Attoparsec.ByteString.Char8 as Parser

sortParser :: Parser.Parser Sort
sortParser = do
    id <- idParser
    actualSortParser id <|> return (SortVariableSort $ SortVariable id)
  where
    actualSortParser id = do
        openCurlyBraceParser
        sorts <- sortListParser
        closedCurlyBraceParser
        return ActualSort
            { actualSortName = id
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
symbolOrAliasRemainderParser id =
    symbolOrAliasRemainderRawParser (SymbolOrAlias id)

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

patternListParser :: Parser.Parser [Pattern]
patternListParser = Parser.sepBy patternParser commaParser

symbolOrAliasPatternRemainderParser :: Id -> Parser.Parser Pattern
symbolOrAliasPatternRemainderParser id = do
    symbolOrAlias <- symbolOrAliasRemainderParser id
    openParenthesisParser
    patterns <- patternListParser
    closedParenthesisParser
    return SymbolOrAliasPattern
        { symbolOrAlias = symbolOrAlias
        , patterns = patterns
        }

variablePatternRemainderParser :: Id -> Parser.Parser Pattern
variablePatternRemainderParser id = do
    colonParser
    sort <- sortParser
    return (VariablePattern Variable { variableName = id, variableSort = sort })

variableParser :: Parser.Parser Variable
variableParser = do
    id <- idParser
    getVariablePattern <$> variablePatternRemainderParser id

variableOrTermPatternParser :: Parser.Parser Pattern
variableOrTermPatternParser = do
    id <- idParser
    c <- Parser.peekChar'
    if c == ':'
        then variablePatternRemainderParser id
        else symbolOrAliasPatternRemainderParser id

equalOrExistsRemainderParser :: Parser.Parser Pattern
equalOrExistsRemainderParser = do
    void (Parser.char 'e')
    c <- Parser.peekChar'
    case c of
        'q' -> mlLexemeParser "quals" *> equalsRemainderParser
        'x' -> mlLexemeParser "xists" *>
               existsForallRemainderParser ExistsPattern

floorOrForallRemainderParser :: Parser.Parser Pattern
floorOrForallRemainderParser = do
    void (Parser.char 'f')
    c <- Parser.peekChar'
    case c of
        'l' -> mlLexemeParser "loor" *> ceilFloorRemainderParser FloorPattern
        'o' -> mlLexemeParser "orall" *>
               existsForallRemainderParser ForallPattern

impliesOrIffRemainderParser :: Parser.Parser Pattern
impliesOrIffRemainderParser = do
    void (Parser.char 'i')
    c <- Parser.peekChar'
    case c of
        'f' -> mlLexemeParser "ff" *> binaryOperatorRemainderParser IffPattern
        'm' -> mlLexemeParser "mplies" *>
               binaryOperatorRemainderParser ImpliesPattern

mlConstructorParser :: Parser.Parser Pattern
mlConstructorParser = do
    Parser.char '\\'
    c <- Parser.peekChar'
    case c of
        'a' -> mlLexemeParser "and" *> binaryOperatorRemainderParser AndPattern
        'b' -> mlLexemeParser "bottom" *> topBottomRemainderParser BottomPattern
        'c' -> mlLexemeParser "ceil" *> ceilFloorRemainderParser CeilPattern
        'e' -> equalOrExistsRemainderParser
        'f' -> floorOrForallRemainderParser
        'i' -> impliesOrIffRemainderParser
        'm' -> mlLexemeParser "mem" *> memRemainderParser
        'n' -> mlLexemeParser "not" *> notRemainderParser
        'o' -> mlLexemeParser "or" *> binaryOperatorRemainderParser OrPattern
        't' -> mlLexemeParser "top" *> topBottomRemainderParser TopPattern
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