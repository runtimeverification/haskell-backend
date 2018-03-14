{-# LANGUAGE ExplicitForAll    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE Rank2Types        #-}
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

unifiedGen
    :: (forall level . MetaOrObject level => level -> Gen (sort level))
    -> Gen (Unified sort)
unifiedGen sortGen = oneof
    [ UnifiedObject <$> sortGen Object
    , UnifiedMeta <$> sortGen Meta
    ]

moduleNameGen :: Gen ModuleName
moduleNameGen = ModuleName <$>
    genericIdGen idFirstChars (idFirstChars ++ idOtherChars)

variableGen :: MetaOrObject level => level -> Gen (Variable level)
variableGen x = pure Variable
    <*> scale (`div` 2) (idGen x)
    <*> scale (`div` 2) (sortGen x)

binaryOperatorGen
    :: MetaOrObject level
    => level
    -> (Sort level -> KorePattern -> KorePattern
        -> b level KorePattern)
    -> Gen (b level KorePattern)
binaryOperatorGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

ceilFloorGen
    :: MetaOrObject level
    => level
    -> (Sort level -> Sort level -> KorePattern -> c level KorePattern)
    -> Gen (c level KorePattern)
ceilFloorGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

existsForallGen
    :: MetaOrObject level
    => level
    -> (Sort level -> Variable level -> KorePattern
        -> q level Variable KorePattern)
    -> Gen (q level Variable KorePattern)
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

andGen :: MetaOrObject level => level -> Gen (And level KorePattern)
andGen x = binaryOperatorGen x And

applicationGen
    :: MetaOrObject level => level -> Gen (Application level KorePattern)
applicationGen x = pure Application
    <*> scale (`div` 2) (symbolOrAliasGen x)
    <*> couple (scale (`div` 4) unifiedPatternGen)

bottomGen :: MetaOrObject level => level -> Gen (Bottom level KorePattern)
bottomGen x = topBottomGen x Bottom

ceilGen :: MetaOrObject level => level -> Gen (Ceil level KorePattern)
ceilGen x = ceilFloorGen x Ceil

equalsGen :: MetaOrObject level => level -> Gen (Equals level KorePattern)
equalsGen x = pure Equals
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

existsGen
    :: MetaOrObject level => level -> Gen (Exists level Variable KorePattern)
existsGen x = existsForallGen x Exists

floorGen :: MetaOrObject level => level -> Gen (Floor level KorePattern)
floorGen x = ceilFloorGen x Floor

forallGen
    :: MetaOrObject level => level -> Gen (Forall level Variable KorePattern)
forallGen x = existsForallGen x Forall

iffGen :: MetaOrObject level => level -> Gen (Iff level KorePattern)
iffGen x = binaryOperatorGen x Iff

impliesGen :: MetaOrObject level => level -> Gen (Implies level KorePattern)
impliesGen x = binaryOperatorGen x Implies

inGen :: MetaOrObject level => level -> Gen (In level KorePattern)
inGen x = pure In
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

nextGen :: MetaOrObject level => level -> Gen (Next level KorePattern)
nextGen x = pure Next
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

notGen :: MetaOrObject level => level -> Gen (Not level KorePattern)
notGen x = pure Not
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

orGen :: MetaOrObject level => level -> Gen (Or level KorePattern)
orGen x = binaryOperatorGen x Or

rewritesGen
    :: MetaOrObject level => level -> Gen (Rewrites level KorePattern)
rewritesGen x = binaryOperatorGen x Rewrites

topGen :: MetaOrObject level => level -> Gen (Top level KorePattern)
topGen x = topBottomGen x Top

patternGen
    :: MetaOrObject level
    => level
    -> Gen (Pattern level Variable KorePattern)
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

unifiedPatternGen :: Gen KorePattern
unifiedPatternGen = sized (\n ->
    if n<=0
        then oneof
            [ asKorePattern . StringLiteralPattern <$> stringLiteralGen
            , asKorePattern . CharLiteralPattern <$> charLiteralGen
            ]
        else frequency
            [ (15, asKorePattern <$> patternGen Meta)
            , (15, asKorePattern <$> patternGen Object)
            , (1, asKorePattern . StringLiteralPattern <$> stringLiteralGen)
            , (1, asKorePattern . CharLiteralPattern <$> charLiteralGen)
            , (1, asKorePattern . NextPattern <$> nextGen Object)
            , (1, asKorePattern . RewritesPattern <$> rewritesGen Object)
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
    <*> couple (scale (`div` 2) (unifiedGen sortVariableGen))
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
