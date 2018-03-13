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

unifiedPatternGen :: Gen UnifiedPattern
unifiedPatternGen = sized (\n ->
    if n<=0
        then oneof
            [ MetaPattern . StringLiteralPattern <$> stringLiteralGen
            , MetaPattern . CharLiteralPattern <$> charLiteralGen
            ]
        else frequency
            [ (15, MetaPattern <$> patternGen unifiedPatternGen Meta)
            , (15, ObjectPattern <$> patternGen unifiedPatternGen Object)
            , (1, MetaPattern . StringLiteralPattern <$> stringLiteralGen)
            , (1, MetaPattern . CharLiteralPattern <$> charLiteralGen)
            , (1, ObjectPattern . NextPattern
                <$> nextGen unifiedPatternGen Object)
            , (1, ObjectPattern . RewritesPattern
                <$> rewritesGen unifiedPatternGen Object)
            ]
    )

sentenceAliasGen
    :: MetaOrObject level
    => Gen attributes -> level -> Gen (SentenceAlias attributes level)
sentenceAliasGen attribGen x = pure SentenceAlias
    <*> scale (`div` 2) (aliasGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) attribGen

sentenceSymbolGen
    :: MetaOrObject level
    => Gen attributes -> level -> Gen (SentenceSymbol attributes level)
sentenceSymbolGen attribGen x = pure SentenceSymbol
    <*> scale (`div` 2) (symbolGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) attribGen

sentenceImportGen :: Gen attributes -> Gen (SentenceImport attributes)
sentenceImportGen attribGen = pure SentenceImport
    <*> scale (`div` 2) moduleNameGen
    <*> scale (`div` 2) attribGen

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
    [ MetaSentenceAliasSentence <$> sentenceAliasGen attributesGen Meta
    , ObjectSentenceAliasSentence <$> sentenceAliasGen attributesGen Object
    , MetaSentenceSymbolSentence <$> sentenceSymbolGen attributesGen Meta
    , ObjectSentenceSymbolSentence <$> sentenceSymbolGen attributesGen Object
    , SentenceImportSentence <$> sentenceImportGen attributesGen
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
