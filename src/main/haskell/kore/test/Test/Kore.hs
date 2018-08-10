module Test.Kore where

import Test.QuickCheck.Gen
       ( Gen, choose, chooseAny, elements, frequency, getSize, listOf, oneof,
       scale, sized, suchThat, vectorOf )

import Data.Functor.Foldable

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.Sentence
import Kore.MetaML.AST
import Kore.Parser.LexemeImpl

couple :: Gen a -> Gen [a]
couple gen = do
    size <- getSize
    if size <= 0
        then return []
        else choose (0,3) >>= (`vectorOf` gen)

couple1 :: Gen a -> Gen [a]
couple1 gen = do
    x <- gen
    xs <- couple gen
    return (x:xs)

{-# ANN genericIdGen ("HLint: ignore Use String" :: String) #-}
genericIdGen :: [Char] -> [Char] -> Gen String
genericIdGen firstChars nextChars = do
    firstChar <- elements firstChars
    body <- listOf (elements nextChars)
    return (firstChar : body)

idGen :: MetaOrObject level => level -> Gen (Id level)
idGen x
    | isObject x = testId <$> objectId
    | otherwise  = testId . ('#' :) <$> objectId
  where
    objectId = genericIdGen idFirstChars (idFirstChars ++ idOtherChars)

stringLiteralGen :: Gen StringLiteral
stringLiteralGen = StringLiteral <$> listOf charGen

charLiteralGen :: Gen CharLiteral
charLiteralGen = CharLiteral <$> charGen

charGen :: Gen Char
charGen =
    suchThat
        (oneof
            [ chooseAny
            , elements "\a\b\f\n\r\t\v\\\"\'"
            , choose ('\32','\127')
            , choose ('\0','\255')
            , choose ('\0','\65535')
            ]
        )
        (/='?')

symbolOrAliasRawGen
    :: MetaOrObject level
    => level
    -> (Id level -> [Sort level] -> s level)
    -> Gen (s level)
symbolOrAliasRawGen x constructor = pure constructor
    <*> scale (`div` 2) (idGen x)
    <*> couple (scale (`div` 2) (sortGen x))

symbolOrAliasDeclarationRawGen
    :: MetaOrObject level
    => level
    -> (Id level -> [SortVariable level] -> s level)
    -> Gen (s level)
symbolOrAliasDeclarationRawGen x constructor = pure constructor
    <*> scale (`div` 2) (idGen x)
    <*> couple (scale (`div` 2) (sortVariableGen x))

symbolOrAliasGen :: MetaOrObject level => level -> Gen (SymbolOrAlias level)
symbolOrAliasGen x = symbolOrAliasRawGen x SymbolOrAlias

symbolGen :: MetaOrObject level => level -> Gen (Symbol level)
symbolGen x = symbolOrAliasDeclarationRawGen x Symbol

aliasGen :: MetaOrObject level => level -> Gen (Alias level)
aliasGen x = symbolOrAliasDeclarationRawGen x Alias

sortVariableGen :: MetaOrObject level => level -> Gen (SortVariable level)
sortVariableGen x = SortVariable <$> idGen x

sortActualGen :: MetaOrObject level => level -> Gen (SortActual level)
sortActualGen x
    | isObject x = pure SortActual
        <*> scale (`div` 2) (idGen x)
        <*> couple (scale (`div` 2) (sortGen x))
    | otherwise = SortActual <$>
        (testId <$> elements (map show metaSortsList)) <*> pure []

sortGen :: MetaOrObject level => level -> Gen (Sort level)
sortGen x = oneof
    [ SortVariableSort <$> sortVariableGen x
    , SortActualSort <$> sortActualGen x
    ]

unifiedSortVariableGen :: Gen UnifiedSortVariable
unifiedSortVariableGen = oneof
    [ UnifiedObject <$> sortVariableGen Object
    , UnifiedMeta <$> sortVariableGen Meta
    ]

moduleNameGen :: Gen ModuleName
moduleNameGen = ModuleName <$>
    genericIdGen idFirstChars (idFirstChars ++ idOtherChars)

variableGen :: MetaOrObject level => level -> Gen (Variable level)
variableGen x = pure Variable
    <*> scale (`div` 2) (idGen x)
    <*> scale (`div` 2) (sortGen x)

unifiedVariableGen :: Gen (Unified Variable)
unifiedVariableGen = scale (`div` 2) $ oneof
    [ UnifiedObject <$> variableGen Object
    , UnifiedMeta <$> variableGen Meta
    ]

unaryOperatorGen
    :: MetaOrObject level
    => Gen child
    -> level
    -> (Sort level -> child -> b level child)
    -> Gen (b level child)
unaryOperatorGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) childGen

binaryOperatorGen
    :: MetaOrObject level
    => Gen child
    -> level
    -> (Sort level -> child -> child -> b level child)
    -> Gen (b level child)
binaryOperatorGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) childGen
    <*> scale (`div` 2) childGen

ceilFloorGen
    :: MetaOrObject level
    => Gen child
    -> level
    -> (Sort level -> Sort level -> child -> c level child)
    -> Gen (c level child)
ceilFloorGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) childGen

equalsInGen
    :: MetaOrObject level
    => Gen child
    -> level
    -> (Sort level -> Sort level -> child -> child -> c level child)
    -> Gen (c level child)
equalsInGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) childGen
    <*> scale (`div` 2) childGen

existsForallGen
    :: MetaOrObject level
    => Gen child
    -> level
    -> (Sort level -> Variable level -> child -> q level Variable child)
    -> Gen (q level Variable child)
existsForallGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (variableGen x)
    <*> scale (`div` 2) childGen

topBottomGen
    :: MetaOrObject level
    => level
    -> (Sort level -> t level child)
    -> Gen (t level child)
topBottomGen x constructor = pure constructor
    <*> sortGen x

andGen :: MetaOrObject level => Gen child -> level -> Gen (And level child)
andGen childGen x = binaryOperatorGen childGen x And

applicationGen
    :: MetaOrObject level
    => Gen child
    -> level
    -> Gen (Application level child)
applicationGen childGen x = pure Application
    <*> scale (`div` 2) (symbolOrAliasGen x)
    <*> couple (scale (`div` 4) childGen)

bottomGen :: MetaOrObject level => level -> Gen (Bottom level child)
bottomGen x = topBottomGen x Bottom

ceilGen :: MetaOrObject level => Gen child -> level -> Gen (Ceil level child)
ceilGen childGen x = ceilFloorGen childGen x Ceil

equalsGen
    :: MetaOrObject level => Gen child -> level -> Gen (Equals level child)
equalsGen childGen x = equalsInGen childGen x Equals

domainValueGen
    :: MetaOrObject level
    => level -> Gen (DomainValue level (Fix (Pattern Meta Variable)))
domainValueGen x = pure DomainValue
    <*> scale (`div` 2) (sortGen x)
    <*> (Fix . StringLiteralPattern <$> stringLiteralGen)

existsGen
    :: MetaOrObject level
    => Gen child
    -> level
    -> Gen (Exists level Variable child)
existsGen childGen x = existsForallGen childGen x Exists

floorGen :: MetaOrObject level => Gen child -> level -> Gen (Floor level child)
floorGen childGen x = ceilFloorGen childGen x Floor

forallGen
    :: MetaOrObject level
    => Gen child -> level -> Gen (Forall level Variable child)
forallGen childGen x = existsForallGen childGen x Forall

iffGen :: MetaOrObject level => Gen child -> level -> Gen (Iff level child)
iffGen childGen x = binaryOperatorGen childGen x Iff

impliesGen
    :: MetaOrObject level => Gen child -> level -> Gen (Implies level child)
impliesGen childGen x = binaryOperatorGen childGen x Implies

inGen :: MetaOrObject level => Gen child -> level -> Gen (In level child)
inGen childGen x = equalsInGen childGen x In

nextGen :: MetaOrObject level => Gen child -> level -> Gen (Next level child)
nextGen childGen x = unaryOperatorGen childGen x Next

notGen :: MetaOrObject level => Gen child -> level -> Gen (Not level child)
notGen childGen x = unaryOperatorGen childGen x Not

orGen :: MetaOrObject level => Gen child -> level -> Gen (Or level child)
orGen childGen x = binaryOperatorGen childGen x Or

rewritesGen
    :: MetaOrObject level => Gen child -> level -> Gen (Rewrites level child)
rewritesGen childGen x = binaryOperatorGen childGen x Rewrites

topGen :: MetaOrObject level => level -> Gen (Top level child)
topGen x = topBottomGen x Top


patternGen
    :: MetaOrObject level
    => Gen child
    -> level
    -> Gen (Pattern level Variable child)
patternGen childGen x =
    oneof
        [ AndPattern <$> andGen childGen x
        , ApplicationPattern <$> applicationGen childGen x
        , BottomPattern <$> bottomGen x
        , CeilPattern <$> ceilGen childGen x
        , EqualsPattern <$> equalsGen childGen x
        , ExistsPattern <$> existsGen childGen x
        , FloorPattern <$> floorGen childGen x
        , ForallPattern <$> forallGen childGen x
        , IffPattern <$> iffGen childGen x
        , ImpliesPattern <$> impliesGen childGen x
        , InPattern <$> inGen childGen x
        , NotPattern <$> notGen childGen x
        , OrPattern <$> orGen childGen x
        , TopPattern <$> topGen x
        , VariablePattern <$> variableGen x
        ]

korePatternGen :: Gen CommonKorePattern
korePatternGen = sized (\n ->
    if n<=0
        then oneof
            [ asKorePattern . StringLiteralPattern <$> stringLiteralGen
            , asKorePattern . CharLiteralPattern <$> charLiteralGen
            ]
        else frequency
            [ (15, asKorePattern <$> patternGen korePatternGen Meta)
            , (15, asKorePattern <$> patternGen korePatternGen Object)
            , (1, asKorePattern . StringLiteralPattern <$> stringLiteralGen)
            , (1, asKorePattern . CharLiteralPattern <$> charLiteralGen)
            , (1, asKorePattern . DomainValuePattern <$> domainValueGen Object)
            , (1, asKorePattern . NextPattern
                <$> nextGen korePatternGen Object)
            , (1, asKorePattern . RewritesPattern
                <$> rewritesGen korePatternGen Object)
            ]
    )

sentenceAliasGen
    :: MetaOrObject level
    => level
    -> Gen (Fix (pat Variable))
    -> Gen (SentenceAlias level pat Variable)
sentenceAliasGen x patGen = pure SentenceAlias
    <*> scale (`div` 2) (aliasGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (patternGen patGen x)
    <*> scale (`div` 2) (patternGen patGen x)
    <*> scale (`div` 2) attributesGen

sentenceSymbolGen
    :: MetaOrObject level
    => level
    -> Gen (SentenceSymbol level pat variable)
sentenceSymbolGen x = pure SentenceSymbol
    <*> scale (`div` 2) (symbolGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) attributesGen

sentenceImportGen
    :: Gen (SentenceImport pat variable)
sentenceImportGen = pure SentenceImport
    <*> scale (`div` 2) moduleNameGen
    <*> scale (`div` 2) attributesGen

sentenceAxiomGen
   :: Gen sortParam
   -> Gen (Fix (pat var))
   -> Gen (SentenceAxiom sortParam pat var)
sentenceAxiomGen sortParamGen patGen =
    pure SentenceAxiom
        <*> couple (scale (`div` 2) sortParamGen)
        <*> scale (`div` 2) patGen
        <*> scale (`div` 2) attributesGen

sentenceSortGen
    :: MetaOrObject level
    => level -> Gen (SentenceSort level pat var)
sentenceSortGen level =
    pure SentenceSort
        <*> scale (`div` 2) (idGen level)
        <*> couple (scale (`div` 2) (sortVariableGen level))
        <*> scale (`div` 2) attributesGen

attributesGen :: Gen Attributes
attributesGen = Attributes <$> couple (scale (`div` 4) korePatternGen)

koreSentenceGen :: Gen KoreSentence
koreSentenceGen = oneof
    [ constructUnifiedSentence SentenceAliasSentence
        <$> sentenceAliasGen Meta korePatternGen
    , constructUnifiedSentence SentenceSymbolSentence
        <$> sentenceSymbolGen Meta
    , constructUnifiedSentence SentenceAliasSentence
        <$> sentenceAliasGen Object korePatternGen
    , constructUnifiedSentence SentenceSymbolSentence
        <$> sentenceSymbolGen Object
    , constructUnifiedSentence SentenceImportSentence
        <$> sentenceImportGen
    , asSentence <$> sentenceAxiomGen unifiedSortVariableGen korePatternGen
    , constructUnifiedSentence SentenceSortSentence
        <$> sentenceSortGen Object
    , constructUnifiedSentence (SentenceHookSentence . SentenceHookedSort)
        <$> sentenceSortGen Object
    , constructUnifiedSentence (SentenceHookSentence . SentenceHookedSymbol)
        <$> sentenceSymbolGen Object
    ]

moduleGen
    :: Gen (sentence sortParam pat variable)
    -> Gen (Module sentence sortParam pat variable)
moduleGen senGen = pure Module
    <*> scale (`div` 2) moduleNameGen
    <*> couple (scale (`div` 2) senGen)
    <*> scale (`div` 2) attributesGen

modulesGen
    :: Gen (sentence sortParam pat variable)
    -> Gen [Module sentence sortParam pat variable]
modulesGen senGen = couple1 (scale (`div` 2) (moduleGen senGen))

definitionGen
    :: Gen (sentence sortParam pat variable)
    -> Gen (Definition sentence sortParam pat variable)
definitionGen senGen = pure Definition
    <*> scale (`div` 2) attributesGen
    <*> scale (`div` 2) (modulesGen senGen)

metaMLPatternGen :: Gen (MetaMLPattern Variable)
metaMLPatternGen = Fix <$> sized (\n ->
    if n<=0
        then oneof
            [ StringLiteralPattern <$> stringLiteralGen
            , CharLiteralPattern <$> charLiteralGen
            ]
        else frequency
            [ (15, patternGen metaMLPatternGen Meta)
            , (1, StringLiteralPattern <$> stringLiteralGen)
            , (1, CharLiteralPattern <$> charLiteralGen)
            ]
    )

metaSentenceGen :: Gen MetaSentence
metaSentenceGen = oneof
    [ (SentenceSymbolSentence <$> sentenceSymbolGen Meta)
    , (SentenceAliasSentence <$> sentenceAliasGen Meta metaMLPatternGen)
    , (SentenceImportSentence
            <$> sentenceImportGen)
    , (SentenceAxiomSentence
            <$> sentenceAxiomGen (sortVariableGen Meta) metaMLPatternGen)
    ]

metaModuleGen :: Gen MetaModule
metaModuleGen = moduleGen metaSentenceGen

testId :: String -> Id level
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }
