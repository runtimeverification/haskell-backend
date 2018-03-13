{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
module Data.Kore.ASTGen where

import           Test.QuickCheck.Gen         (Gen, choose, chooseAny, elements,
                                              frequency, getSize, listOf, oneof,
                                              scale, sized, suchThat, vectorOf)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.Parser.LexemeImpl

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

{-# ANN genericIdGen "HLint: ignore Use String" #-}
genericIdGen :: [Char] -> [Char] -> Gen String
genericIdGen firstChars nextChars = do
    firstChar <- elements firstChars
    body <- listOf (elements nextChars)
    return (firstChar : body)

idGen :: MetaOrObject level => level -> Gen (Id level)
idGen x
    | isObject x = Id <$> objectId
    | otherwise  = Id . ('#' :) <$> objectId
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
        (Id <$> elements (map show metaSortsList)) <*> pure []

sortGen :: MetaOrObject level => level -> Gen (Sort level)
sortGen x = oneof
    [ SortVariableSort <$> sortVariableGen x
    , SortActualSort <$> sortActualGen x
    ]

unifiedSortVariableGen :: Gen UnifiedSortVariable
unifiedSortVariableGen = oneof
    [ ObjectSortVariable <$> sortVariableGen Object
    , MetaSortVariable <$> sortVariableGen Meta
    ]

moduleNameGen :: Gen ModuleName
moduleNameGen = ModuleName <$>
    genericIdGen idFirstChars (idFirstChars ++ idOtherChars)

variableGen :: MetaOrObject level => level -> Gen (Variable level)
variableGen x = pure Variable
    <*> scale (`div` 2) (idGen x)
    <*> scale (`div` 2) (sortGen x)

unifiedVariableGen :: Gen (UnifiedVariable Variable)
unifiedVariableGen = scale (`div` 2) $ oneof
    [ ObjectVariable <$> variableGen Object
    , MetaVariable <$> variableGen Meta
    ]

binaryOperatorGen
    :: MetaOrObject level
    => level
    -> (Sort level -> UnifiedPattern -> UnifiedPattern
        -> b level UnifiedPattern)
    -> Gen (b level UnifiedPattern)
binaryOperatorGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

ceilFloorGen
    :: MetaOrObject level
    => level
    -> (Sort level -> Sort level -> UnifiedPattern -> c level UnifiedPattern)
    -> Gen (c level UnifiedPattern)
ceilFloorGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

existsForallGen
    :: MetaOrObject level
    => level
    -> (Sort level -> Variable level -> UnifiedPattern
        -> q level Variable UnifiedPattern)
    -> Gen (q level Variable UnifiedPattern)
existsForallGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (variableGen x)
    <*> scale (`div` 2) unifiedPatternGen

topBottomGen
    :: MetaOrObject level
    => level
    -> (Sort level -> t level p)
    -> Gen (t level p)
topBottomGen x constructor = pure constructor
    <*> sortGen x

andGen :: MetaOrObject level => level -> Gen (And level UnifiedPattern)
andGen x = binaryOperatorGen x And

applicationGen
    :: MetaOrObject level => level -> Gen (Application level UnifiedPattern)
applicationGen x = pure Application
    <*> scale (`div` 2) (symbolOrAliasGen x)
    <*> couple (scale (`div` 4) unifiedPatternGen)

bottomGen :: MetaOrObject level => level -> Gen (Bottom level UnifiedPattern)
bottomGen x = topBottomGen x Bottom

ceilGen :: MetaOrObject level => level -> Gen (Ceil level UnifiedPattern)
ceilGen x = ceilFloorGen x Ceil

equalsGen :: MetaOrObject level => level -> Gen (Equals level UnifiedPattern)
equalsGen x = pure Equals
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

existsGen
    :: MetaOrObject level => level -> Gen (Exists level Variable UnifiedPattern)
existsGen x = existsForallGen x Exists

floorGen :: MetaOrObject level => level -> Gen (Floor level UnifiedPattern)
floorGen x = ceilFloorGen x Floor

forallGen
    :: MetaOrObject level => level -> Gen (Forall level Variable UnifiedPattern)
forallGen x = existsForallGen x Forall

iffGen :: MetaOrObject level => level -> Gen (Iff level UnifiedPattern)
iffGen x = binaryOperatorGen x Iff

impliesGen :: MetaOrObject level => level -> Gen (Implies level UnifiedPattern)
impliesGen x = binaryOperatorGen x Implies

inGen :: MetaOrObject level => level -> Gen (In level UnifiedPattern)
inGen x = pure In
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

nextGen :: MetaOrObject level => level -> Gen (Next level UnifiedPattern)
nextGen x = pure Next
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

notGen :: MetaOrObject level => level -> Gen (Not level UnifiedPattern)
notGen x = pure Not
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

orGen :: MetaOrObject level => level -> Gen (Or level UnifiedPattern)
orGen x = binaryOperatorGen x Or

rewritesGen
    :: MetaOrObject level => level -> Gen (Rewrites level UnifiedPattern)
rewritesGen x = binaryOperatorGen x Rewrites

topGen :: MetaOrObject level => level -> Gen (Top level UnifiedPattern)
topGen x = topBottomGen x Top

patternGen
    :: MetaOrObject level
    => level
    -> Gen (Pattern level Variable UnifiedPattern)
patternGen x =
    oneof
        [ AndPattern <$> andGen x
        , ApplicationPattern <$> applicationGen x
        , BottomPattern <$> bottomGen x
        , CeilPattern <$> ceilGen x
        , EqualsPattern <$> equalsGen x
        , ExistsPattern <$> existsGen x
        , FloorPattern <$> floorGen x
        , ForallPattern <$> forallGen x
        , IffPattern <$> iffGen x
        , ImpliesPattern <$> impliesGen x
        , InPattern <$> inGen x
        , NotPattern <$> notGen x
        , OrPattern <$> orGen x
        , TopPattern <$> topGen x
        , VariablePattern <$> variableGen x
        ]

unifiedPatternGen :: Gen UnifiedPattern
unifiedPatternGen = sized (\n ->
    if n<=0
        then oneof
            [ MetaPattern . StringLiteralPattern <$> stringLiteralGen
            , MetaPattern . CharLiteralPattern <$> charLiteralGen
            ]
        else frequency
            [ (15, MetaPattern <$> patternGen Meta)
            , (15, ObjectPattern <$> patternGen Object)
            , (1, MetaPattern . StringLiteralPattern <$> stringLiteralGen)
            , (1, MetaPattern . CharLiteralPattern <$> charLiteralGen)
            , (1, ObjectPattern . NextPattern <$> nextGen Object)
            , (1, ObjectPattern . RewritesPattern <$> rewritesGen Object)
            ]
    )

sentenceAliasGen :: MetaOrObject level => level -> Gen (KoreSentenceAlias level)
sentenceAliasGen x = pure SentenceAlias
    <*> scale (`div` 2) (aliasGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) attributesGen

sentenceSymbolGen
    :: MetaOrObject level => level -> Gen (KoreSentenceSymbol level)
sentenceSymbolGen x = pure SentenceSymbol
    <*> scale (`div` 2) (symbolGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) attributesGen

sentenceImportGen :: Gen KoreSentenceImport
sentenceImportGen = pure SentenceImport
    <*> scale (`div` 2) moduleNameGen
    <*> scale (`div` 2) attributesGen

sentenceAxiomGen :: Gen KoreSentenceAxiom
sentenceAxiomGen = pure SentenceAxiom
    <*> couple (scale (`div` 2) unifiedSortVariableGen)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) attributesGen

sentenceSortGen :: Gen KoreSentenceSort
sentenceSortGen = pure SentenceSort
    <*> scale (`div` 2) (idGen Object)
    <*> couple (scale (`div` 2) (sortVariableGen Object))
    <*> scale (`div` 2) attributesGen

attributesGen :: Gen Attributes
attributesGen = Attributes <$> couple (scale (`div` 4) unifiedPatternGen)

sentenceGen :: Gen Sentence
sentenceGen = oneof
    [ MetaSentenceAliasSentence <$> sentenceAliasGen Meta
    , ObjectSentenceAliasSentence <$> sentenceAliasGen Object
    , MetaSentenceSymbolSentence <$> sentenceSymbolGen Meta
    , ObjectSentenceSymbolSentence <$> sentenceSymbolGen Object
    , SentenceImportSentence <$> sentenceImportGen
    , SentenceAxiomSentence <$> sentenceAxiomGen
    , SentenceSortSentence <$> sentenceSortGen
    ]

moduleGen :: Gen Module
moduleGen = pure Module
    <*> scale (`div` 2) moduleNameGen
    <*> couple (scale (`div` 2) sentenceGen)
    <*> scale (`div` 2) attributesGen

modulesGen :: Gen [Module]
modulesGen = couple1 (scale (`div` 2) moduleGen)

definitionGen :: Gen Definition
definitionGen = pure Definition
    <*> scale (`div` 2) attributesGen
    <*> scale (`div` 2) modulesGen
