{-# LANGUAGE ExistentialQuantification #-}
module KoreParserImpl where

import           KoreAST
import           KoreLexeme

import           Control.Applicative              ((<|>))
import           Control.Monad                    (void, when)

import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser

sortVariableParser :: IsMeta a => a -> Parser (SortVariable a)
sortVariableParser x = SortVariable <$> idParser x

unifiedSortVariableParser :: Parser UnifiedSortVariable
unifiedSortVariableParser = do
    c <- Parser.peekChar'
    if c == '#'
        then MetaSortVariable <$> sortVariableParser Meta
        else ObjectSortVariable <$> sortVariableParser Object

sortVariableListParser :: Parser [UnifiedSortVariable]
sortVariableListParser = Parser.sepBy unifiedSortVariableParser commaParser

sortParser :: IsMeta a => a -> Parser (Sort a)
sortParser x = do
    identifier <- idParser x
    actualSortParser identifier <|>
        return (SortVariableSort $ SortVariable identifier)
  where
    actualSortParser identifier = do
        sorts <- inCurlyBracesParser (sortListParser x)
        when (metaType x == MetaType) (checkMetaSort identifier sorts)
        return ActualSort
            { actualSortName = identifier
            , actualSortSorts = sorts
            }

checkMetaSort :: Id a -> [Sort a] -> Parser ()
checkMetaSort identifier [] = checkMetaSort' (getId identifier)
  where
    checkMetaSort' metaId =
        if metaId `elem`  --TODO: optimize ?
            [ "#Char"
            , "#CharList"
            , "#Pattern"
            , "#PatternList"
            , "#ObjectSort"
            , "#SortList"
            , "#String"
            , "#ObjectSymbol"
            , "#SymbolList"
            , "#Variable"
            , "#VariableList"
            ]
            then return ()
            else fail ("metaSortParser: Invalid constructor: '" ++
                metaId ++ "'.")

sortListParser :: IsMeta a => a -> Parser [Sort a]
sortListParser x = Parser.sepBy (sortParser x) commaParser

symbolOrAliasRemainderRawParser
    :: IsMeta a => a -> ([Sort a] -> (m a)) -> Parser (m a)
symbolOrAliasRemainderRawParser x constructor =
    constructor <$> inCurlyBracesParser (sortListParser x)

symbolOrAliasRawParser
    :: IsMeta a => a -> (Id a -> [Sort a] -> m a) -> Parser (m a)
symbolOrAliasRawParser x constructor = do
    headConstructor <- idParser x
    symbolOrAliasRemainderRawParser x (constructor headConstructor)

aliasParser :: IsMeta a => a -> Parser (Alias a)
aliasParser x = symbolOrAliasRawParser x Alias

symbolParser :: IsMeta a => a -> Parser (Symbol a)
symbolParser x = symbolOrAliasRawParser x Symbol

symbolOrAliasRemainderParser
    :: IsMeta a => a -> Id a -> Parser (SymbolOrAlias a)
symbolOrAliasRemainderParser x identifier =
    symbolOrAliasRemainderRawParser x (SymbolOrAlias identifier)

unaryOperatorRemainderParser
    :: IsMeta a => a -> (Sort a -> Pattern -> Pattern) -> Parser Pattern
unaryOperatorRemainderParser x constructor =
    pure constructor
        <*> inCurlyBracesRemainderParser (sortParser x)
        <*> inParenthesesParser patternParser

{-
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
-}

getMeta :: IsMeta a => (a -> Parser Pattern) -> Parser Pattern
getMeta pa = do
    c <- Parser.peekChar'
    if c == '#'
        then (pa Meta)
        else (pa Object)

mlConstructorParser :: Parser Pattern
mlConstructorParser = do
    void (Parser.char '\\')
    mlPatternParser
  where
    mlPatternParser = keywordBasedParsers
        [ {-("and", binaryOperatorRemainderParser AndPattern)
        , ("bottom", topBottomRemainderParser BottomPattern)
        , ("ceil", ceilFloorRemainderParser CeilPattern)
        , ("equals", equalsLikeRemainderParser EqualsPattern)
        , ("exists", existsForallRemainderParser ExistsPattern)
        , ("floor", ceilFloorRemainderParser FloorPattern)
        , ("forall", existsForallRemainderParser ForallPattern)
        , ("iff", binaryOperatorRemainderParser IffPattern)
        , ("implies", binaryOperatorRemainderParser ImpliesPattern)
        , ("mem", memRemainderParser)
        ,-} ("not", unaryOperatorRemainderParser (openCurlyBrace *> getMeta) NotPattern)
{-
        , ("or", binaryOperatorRemainderParser OrPattern)
        , ("top", topBottomRemainderParser TopPattern)
        -}
        ]
{-
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
-}