{-# LANGUAGE FlexibleInstances #-}
module Data.Kore.ASTGen where

import           Test.QuickCheck.Gen
import           Test.Tasty.QuickCheck

import           Data.Kore.AST
import           Data.Kore.Parser.CString
import           Data.Kore.Parser.LexemeImpl


couple :: Gen a -> Gen [a]
couple gen = do
  n <- choose (0,2)
  vectorOf n gen

genericIdGen :: [Char] -> [Char] -> Gen (String)
genericIdGen firstChars nextChars = do
    firstChar <- elements firstChars
    body <- listOf (elements nextChars)
    return (firstChar : body)

idGen :: IsMeta a => a -> Gen (Id a)
idGen x
    | koreLevel x == ObjectLevel = Id <$> objectId
    | otherwise                  = Id <$> ('#' :) <$> objectId
  where
    objectId = genericIdGen idFirstChars (idFirstChars ++ idOtherChars)

stringLiteralGen :: Gen StringLiteral
stringLiteralGen = StringLiteral <$> listOf chooseAny

symbolOrAliasRawGen
    :: IsMeta a
    => a -> (Id a -> [Sort a] -> s a)
    -> Gen (s a)
symbolOrAliasRawGen x constructor = pure constructor
    <*> scale (`div` 2) (idGen x)
    <*> couple (scale (`div` 2) (sortGen x))

symbolOrAliasGen :: IsMeta a => a -> Gen (SymbolOrAlias a)
symbolOrAliasGen x = symbolOrAliasRawGen x SymbolOrAlias

symbolGen :: IsMeta a => a -> Gen (Symbol a)
symbolGen x = symbolOrAliasRawGen x Symbol

aliasGen :: IsMeta a => a -> Gen (Alias a)
aliasGen x = symbolOrAliasRawGen x Alias

sortVariableGen :: IsMeta a => a -> Gen (SortVariable a)
sortVariableGen x = SortVariable <$> idGen x

sortActualGen :: IsMeta a => a -> Gen (SortActual a)
sortActualGen x
    | koreLevel x == ObjectLevel = pure SortActual
        <*> scale (`div` 2) (idGen x)
        <*> couple (scale (`div` 2) (sortGen x))
    | otherwise = SortActual <$>
        (Id <$> elements (map show metaSortsList)) <*> pure []

sortGen :: IsMeta a => a -> Gen (Sort a)
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

variableGen :: IsMeta a => a -> Gen (Variable a)
variableGen x = pure Variable
    <*> scale (`div` 2) (idGen x)
    <*> scale (`div` 2) (sortGen x)

unifiedVariableGen :: Gen UnifiedVariable
unifiedVariableGen = scale (`div` 2) $ oneof
    [ ObjectVariable <$> variableGen Object
    , MetaVariable <$> variableGen Meta
    ]

binaryOperatorGen
    :: IsMeta a
    => a -> (Sort a -> UnifiedPattern -> UnifiedPattern -> b a)
    -> Gen (b a)
binaryOperatorGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

ceilFloorGen
    :: IsMeta a
    => a -> (Sort a -> Sort a -> UnifiedPattern -> c a)
    -> Gen (c a)
ceilFloorGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

existsForallGen
    :: IsMeta a
    => a -> (Sort a -> UnifiedVariable -> UnifiedPattern -> q a)
    -> Gen (q a)
existsForallGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedVariableGen
    <*> scale (`div` 2) unifiedPatternGen

topBottomGen
    :: IsMeta a
    => a -> (Sort a -> t a)
    -> Gen (t a)
topBottomGen x constructor = pure constructor
    <*> sortGen x

andGen :: IsMeta a => a -> Gen (And a)
andGen x = binaryOperatorGen x And

applicationGen :: IsMeta a => a -> Gen (Application a)
applicationGen x = pure Application
    <*> scale (`div` 2) (symbolOrAliasGen x)
    <*> couple (scale (`div` 4) unifiedPatternGen)

bottomGen :: IsMeta a => a -> Gen (Bottom a)
bottomGen x = topBottomGen x Bottom

ceilGen :: IsMeta a => a -> Gen (Ceil a)
ceilGen x = ceilFloorGen x Ceil

equalsGen :: IsMeta a => a -> Gen (Equals a)
equalsGen x = pure Equals
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

existsGen :: IsMeta a => a -> Gen (Exists a)
existsGen x = existsForallGen x Exists

floorGen :: IsMeta a => a -> Gen (Floor a)
floorGen x = ceilFloorGen x Floor

forallGen :: IsMeta a => a -> Gen (Forall a)
forallGen x = existsForallGen x Forall

iffGen :: IsMeta a => a -> Gen (Iff a)
iffGen x = binaryOperatorGen x Iff

impliesGen :: IsMeta a => a -> Gen (Implies a)
impliesGen x = binaryOperatorGen x Implies

memGen :: IsMeta a => a -> Gen (Mem a)
memGen x = pure Mem
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedVariableGen
    <*> scale (`div` 2) unifiedPatternGen

notGen :: IsMeta a => a -> Gen (Not a)
notGen x = pure Not
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

orGen :: IsMeta a => a -> Gen (Or a)
orGen x = binaryOperatorGen x Or

topGen :: IsMeta a => a -> Gen (Top a)
topGen x = topBottomGen x Top

patternGen :: IsMeta a => a -> Gen (Pattern a)
patternGen x =
    suchThat ( oneof
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
        , MemPattern <$> memGen x
        , NotPattern <$> notGen x
        , OrPattern <$> orGen x
        , StringLiteralPattern <$> stringLiteralGen
        , TopPattern <$> topGen x
        , VariablePattern <$> variableGen x
        ]
    ) checkStringLiteralMeta
  where
    checkStringLiteralMeta (StringLiteralPattern _) = koreLevel x == MetaLevel
    checkStringLiteralMeta _                        = True

unifiedPatternGen :: Gen UnifiedPattern
unifiedPatternGen = oneof
    [ MetaPattern <$> patternGen Meta
    , ObjectPattern <$> patternGen Object
    ]

sentenceAliasGen :: IsMeta a => a -> Gen (SentenceAlias a)
sentenceAliasGen x = pure SentenceAlias
    <*> scale (`div` 2) (aliasGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) attributesGen

sentenceSymbolGen :: IsMeta a => a -> Gen (SentenceSymbol a)
sentenceSymbolGen x = pure SentenceSymbol
    <*> scale (`div` 2) (symbolGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) attributesGen

sentenceAxiomGen :: Gen SentenceAxiom
sentenceAxiomGen = pure SentenceAxiom
    <*> couple (scale (`div` 2) unifiedSortVariableGen)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) attributesGen

sentenceSortGen :: Gen SentenceSort
sentenceSortGen = pure SentenceSort
    <*> couple (scale (`div` 2) unifiedSortVariableGen)
    <*> scale (`div` 2) (sortGen Object)
    <*> scale (`div` 2) attributesGen

attributesGen :: Gen Attributes
attributesGen = Attributes <$> couple (scale (`div` 4) unifiedPatternGen)

sentenceGen :: Gen Sentence
sentenceGen = oneof
    [ MetaSentenceAliasSentence <$> sentenceAliasGen Meta
    , ObjectSentenceAliasSentence <$> sentenceAliasGen Object
    , MetaSentenceSymbolSentence <$> sentenceSymbolGen Meta
    , ObjectSentenceSymbolSentence <$> sentenceSymbolGen Object
    , SentenceAxiomSentence <$> sentenceAxiomGen
    , SentenceSortSentence <$> sentenceSortGen
    ]

moduleGen :: Gen Module
moduleGen = pure Module
    <*> scale (`div` 2) moduleNameGen
    <*> couple (scale (`div` 2) sentenceGen)
    <*> scale (`div` 2) attributesGen

definitionGen :: Gen Definition
definitionGen = pure Definition
    <*> scale (`div` 2) attributesGen
    <*> scale (`div` 2) moduleGen
