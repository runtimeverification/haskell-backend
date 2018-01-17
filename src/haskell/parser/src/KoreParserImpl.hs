module KoreParserImpl where

import           KoreAST
import           KoreLexeme

import           Control.Applicative              ((<|>))
import           Control.Monad                    (void, when)

import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser
import           Data.Maybe                       (isJust)

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
    c <- Parser.peekChar
    case c of
        Just '{' -> actualSortParser identifier
        _        -> return (SortVariableSort $ SortVariable identifier)
  where
    actualSortParser identifier = do
        sorts <- inCurlyBracesParser (sortListParser x)
        when (metaType x == MetaType) (checkMetaSort identifier sorts)
        return $ SortActualSort $ SortActual
            { sortActualName = identifier
            , sortActualSorts = sorts
            }

checkMetaSort :: Show a => Id a -> [Sort a] -> Parser ()
checkMetaSort identifier [] =
    if isJust (metaSortParser metaId)
        then return ()
        else fail ("metaSortParser: Invalid constructor: '" ++ metaId ++ "'.")
  where
    metaId = getId identifier
checkMetaSort _ l = fail "metaSortParser: Non empty parameter sorts"

metaSort :: MetaSortType -> Sort Meta
metaSort sortType = SortActualSort SortActual
    { sortActualName = Id (show sortType)
    , sortActualSorts = []}

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
    :: IsMeta a
    => a -> (Sort a -> UnifiedPattern -> m a) -> Parser (m a)
unaryOperatorRemainderParser x constructor =
    pure constructor
        <*> inCurlyBracesRemainderParser (sortParser x)
        <*> inParenthesesParser patternParser

binaryOperatorRemainderParser
    :: IsMeta a
    => a -> (Sort a -> UnifiedPattern -> UnifiedPattern -> m a)
    -> Parser (m a)
binaryOperatorRemainderParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    (pattern1, pattern2) <-
        parenPairParser patternParser patternParser
    return (constructor sort pattern1 pattern2)

existsForallRemainderParser
    :: IsMeta a
    => a -> (Sort a -> UnifiedVariable -> UnifiedPattern -> m a)
    -> Parser (m a)
existsForallRemainderParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    (variable, pattern) <-
        parenPairParser unifiedVariableParser patternParser
    return (constructor sort variable pattern)

ceilFloorRemainderParser
    :: IsMeta a
    => a -> (Sort a -> Sort a -> UnifiedPattern -> m a)
    -> Parser (m a)
ceilFloorRemainderParser x constructor = do
    (sort1, sort2) <- curlyPairRemainderParser (sortParser x)
    pattern <- inParenthesesParser patternParser
    return (constructor sort1 sort2 pattern)

memRemainderParser
    :: IsMeta a => a -> Parser (Mem a)
memRemainderParser x = do
    (sort1, sort2) <- curlyPairRemainderParser (sortParser x)
    (variable, pattern) <-
        parenPairParser unifiedVariableParser patternParser
    return Mem
           { memFirstSort = sort1
           , memSecondSort = sort2
           , memVariable = variable
           , memPattern = pattern
           }

equalsLikeRemainderParser
    :: IsMeta a
    => a -> (Sort a -> Sort a -> UnifiedPattern -> UnifiedPattern -> m a)
    -> Parser (m a)
equalsLikeRemainderParser x constructor = do
    (sort1, sort2) <- curlyPairRemainderParser (sortParser x)
    (pattern1, pattern2) <-
        parenPairParser patternParser patternParser
    return (constructor sort1 sort2 pattern1 pattern2)

topBottomRemainderParser
    :: IsMeta a => a -> (Sort a -> Pattern a) -> Parser (Pattern a)
topBottomRemainderParser x constructor = do
    sort <- inCurlyBracesRemainderParser (sortParser x)
    inParenthesesParser (return ())
    return (constructor sort)

symbolOrAliasPatternRemainderParser
    :: IsMeta a => a -> Id a -> Parser (Pattern a)
symbolOrAliasPatternRemainderParser x identifier = ApplicationPattern <$>
    ( pure Application
        <*> symbolOrAliasRemainderParser x identifier
        <*> inParenthesesParser patternListParser
    )

variableRemainderParser
    :: IsMeta a => a -> Id a -> Parser (Variable a)
variableRemainderParser x identifier = do
    colonParser
    sort <- sortParser x
    return Variable
        { variableName = identifier
        , variableSort = sort
        }

variableParser
    :: IsMeta a => a -> Parser (Variable a)
variableParser x = idParser x >>= variableRemainderParser x

unifiedVariableParser :: Parser UnifiedVariable
unifiedVariableParser = do
    c <- Parser.peekChar'
    if c == '#'
        then MetaVariable <$> variableParser Meta
        else ObjectVariable <$> variableParser Object

unifiedVariableOrTermPatternParser :: Parser UnifiedPattern
unifiedVariableOrTermPatternParser = do
    c <- Parser.peekChar'
    if c == '#'
        then MetaPattern <$> variableOrTermPatternParser Meta
        else ObjectPattern <$> variableOrTermPatternParser Object

variableOrTermPatternParser
    :: IsMeta a => a -> Parser (Pattern a)
variableOrTermPatternParser x = do
    identifier <- idParser x
    c <- Parser.peekChar'
    if c == ':'
        then VariablePattern <$> variableRemainderParser x identifier
        else symbolOrAliasPatternRemainderParser x identifier

data PatternType
    = AndPatternType
    | BottomPatternType
    | CeilPatternType
    | EqualsPatternType
    | ExistsPatternType
    | FloorPatternType
    | ForallPatternType
    | IffPatternType
    | ImpliesPatternType
    | MemPatternType
    | NotPatternType
    | OrPatternType
    | TopPatternType

mlConstructorParser :: Parser UnifiedPattern
mlConstructorParser = do
    void (Parser.char '\\')
    mlPatternParser
  where
    mlPatternParser = keywordBasedParsers
        [ ("and", mlConstructorRemainderParser AndPatternType)
        , ("bottom", mlConstructorRemainderParser BottomPatternType)
        , ("ceil", mlConstructorRemainderParser CeilPatternType)
        , ("equals", mlConstructorRemainderParser EqualsPatternType)
        , ("exists", mlConstructorRemainderParser ExistsPatternType)
        , ("floor", mlConstructorRemainderParser FloorPatternType)
        , ("forall", mlConstructorRemainderParser ForallPatternType)
        , ("iff", mlConstructorRemainderParser IffPatternType)
        , ("implies", mlConstructorRemainderParser ImpliesPatternType)
        , ("mem", mlConstructorRemainderParser MemPatternType)
        , ("not", mlConstructorRemainderParser NotPatternType)
        , ("or", mlConstructorRemainderParser OrPatternType)
        , ("top", mlConstructorRemainderParser TopPatternType)
        ]
    mlConstructorRemainderParser patternType = do
        openCurlyBraceParser
        c <- Parser.peekChar'
        if c == '#'
            then MetaPattern <$> mlConstructorRemainderParser' Meta patternType
            else ObjectPattern <$>
                mlConstructorRemainderParser' Object patternType
    mlConstructorRemainderParser' x patternType =
        case patternType of
            AndPatternType -> AndPattern <$>
                binaryOperatorRemainderParser x And
            BottomPatternType -> topBottomRemainderParser x BottomPattern
            CeilPatternType -> CeilPattern <$>
                ceilFloorRemainderParser x Ceil
            EqualsPatternType -> EqualsPattern <$>
                equalsLikeRemainderParser x Equals
            ExistsPatternType -> ExistsPattern <$>
                existsForallRemainderParser x Exists
            FloorPatternType -> FloorPattern <$>
                ceilFloorRemainderParser x Floor
            ForallPatternType -> ForallPattern <$>
                existsForallRemainderParser x Forall
            IffPatternType -> IffPattern <$>
                binaryOperatorRemainderParser x Iff
            ImpliesPatternType -> ImpliesPattern <$>
                binaryOperatorRemainderParser x Implies
            MemPatternType -> MemPattern <$>
                memRemainderParser x
            NotPatternType -> NotPattern <$>
                unaryOperatorRemainderParser x Not
            OrPatternType -> OrPattern <$>
                binaryOperatorRemainderParser x Or
            TopPatternType -> topBottomRemainderParser x TopPattern

patternParser :: Parser UnifiedPattern
patternParser = do
    c <- Parser.peekChar'
    case c of
        '\\' -> mlConstructorParser
        '"'  -> MetaPattern <$> StringLiteralPattern <$> stringLiteralParser
        _    -> unifiedVariableOrTermPatternParser

patternListParser :: Parser [UnifiedPattern]
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
    sentences <- Parser.many' sentenceParser
    mlLexemeParser "endmodule"
    attributes <- attributesParser
    return Module
           { moduleName = name
           , moduleSentences = sentences
           , moduleAttributes = attributes
           }

data SentenceType
    = AliasSentenceType
    | SymbolSentenceType


sentenceParser :: Parser Sentence
sentenceParser = keywordBasedParsers
    [ ( "alias", sentenceConstructorRemainderParser AliasSentenceType)
    , ( "axiom", axiomSentenceRemainderParser )
    , ( "sort", sortSentenceRemainderParser )
    , ( "symbol", sentenceConstructorRemainderParser SymbolSentenceType)
    ]
  where
    sentenceConstructorRemainderParser sentenceType = do
        c <- Parser.peekChar'
        case (c, sentenceType) of
            ('#', AliasSentenceType) -> MetaSentenceAliasSentence <$>
                aliasSymbolSentenceRemainderParser Meta (aliasParser Meta)
                    SentenceAlias
            ('#', SymbolSentenceType) -> MetaSentenceSymbolSentence <$>
                aliasSymbolSentenceRemainderParser Meta (symbolParser Meta)
                    SentenceSymbol
            (_, AliasSentenceType) -> ObjectSentenceAliasSentence <$>
                aliasSymbolSentenceRemainderParser Object (aliasParser Object)
                    SentenceAlias
            (_, SymbolSentenceType) -> ObjectSentenceSymbolSentence <$>
                aliasSymbolSentenceRemainderParser Object (symbolParser Object)
                    SentenceSymbol

aliasSymbolSentenceRemainderParser
    :: IsMeta a
    => a
    -> Parser (m a)
    -> (m a -> [Sort a] -> Sort a -> Attributes -> as a)
    -> Parser (as a)
aliasSymbolSentenceRemainderParser  x aliasSymbolParser constructor = do
    aliasSymbol <- aliasSymbolParser
    sorts <- inParenthesesParser (sortListParser x)
    colonParser
    resultSort <- sortParser x
    attributes <- attributesParser
    return (constructor aliasSymbol sorts resultSort attributes)

axiomSentenceRemainderParser :: Parser Sentence
axiomSentenceRemainderParser = SentenceAxiomSentence <$>
    ( pure SentenceAxiom
        <*> inCurlyBracesParser sortVariableListParser
        <*> patternParser
        <*> attributesParser
    )

sortSentenceRemainderParser :: Parser Sentence
sortSentenceRemainderParser = SentenceSortSentence <$>
    ( pure SentenceSort
        <*> inCurlyBracesParser sortVariableListParser
        <*> sortParser Object
        <*> attributesParser
    )
