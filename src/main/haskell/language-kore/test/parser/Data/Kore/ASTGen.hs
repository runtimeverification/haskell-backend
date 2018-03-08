{-# LANGUAGE FlexibleInstances #-}
module Data.Kore.ASTGen where

import           Test.QuickCheck.Gen         (Gen, choose, chooseAny, elements,
                                              getSize, listOf, oneof, scale,
                                              sized, suchThat, vectorOf)

import           Data.Kore.AST
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

idGen :: IsMeta a => a -> Gen (Id a)
idGen x
    | koreLevel x == ObjectLevel = Id <$> objectId
    | otherwise                  = Id . ('#' :) <$> objectId
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
    :: IsMeta a
    => a
    -> (Id a -> [Sort a] -> s a)
    -> Gen (s a)
symbolOrAliasRawGen x constructor = pure constructor
    <*> scale (`div` 2) (idGen x)
    <*> couple (scale (`div` 2) (sortGen x))

symbolOrAliasDeclarationRawGen
    :: IsMeta a
    => a
    -> (Id a -> [SortVariable a] -> s a)
    -> Gen (s a)
symbolOrAliasDeclarationRawGen x constructor = pure constructor
    <*> scale (`div` 2) (idGen x)
    <*> couple (scale (`div` 2) (sortVariableGen x))

symbolOrAliasGen :: IsMeta a => a -> Gen (SymbolOrAlias a)
symbolOrAliasGen x = symbolOrAliasRawGen x SymbolOrAlias

symbolGen :: IsMeta a => a -> Gen (Symbol a)
symbolGen x = symbolOrAliasDeclarationRawGen x Symbol

aliasGen :: IsMeta a => a -> Gen (Alias a)
aliasGen x = symbolOrAliasDeclarationRawGen x Alias

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

unifiedVariableGen :: Gen (UnifiedVariable Variable)
unifiedVariableGen = scale (`div` 2) $ oneof
    [ ObjectVariable <$> variableGen Object
    , MetaVariable <$> variableGen Meta
    ]

binaryOperatorGen
    :: IsMeta a
    => a
    -> (Sort a -> UnifiedPattern -> UnifiedPattern -> b a UnifiedPattern)
    -> Gen (b a UnifiedPattern)
binaryOperatorGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

ceilFloorGen
    :: IsMeta a
    => a
    -> (Sort a -> Sort a -> UnifiedPattern -> c a UnifiedPattern)
    -> Gen (c a UnifiedPattern)
ceilFloorGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

existsForallGen
    :: IsMeta a
    => a
    -> (Sort a -> Variable a -> UnifiedPattern
        -> q a Variable UnifiedPattern)
    -> Gen (q a Variable UnifiedPattern)
existsForallGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (variableGen x)
    <*> scale (`div` 2) unifiedPatternGen

topBottomGen
    :: IsMeta a
    => a
    -> (Sort a -> t a p)
    -> Gen (t a p)
topBottomGen x constructor = pure constructor
    <*> sortGen x

andGen :: IsMeta a => a -> Gen (And a UnifiedPattern)
andGen x = binaryOperatorGen x And

applicationGen :: IsMeta a => a -> Gen (Application a UnifiedPattern)
applicationGen x = pure Application
    <*> scale (`div` 2) (symbolOrAliasGen x)
    <*> couple (scale (`div` 4) unifiedPatternGen)

bottomGen :: IsMeta a => a -> Gen (Bottom a UnifiedPattern)
bottomGen x = topBottomGen x Bottom

ceilGen :: IsMeta a => a -> Gen (Ceil a UnifiedPattern)
ceilGen x = ceilFloorGen x Ceil

equalsGen :: IsMeta a => a -> Gen (Equals a UnifiedPattern)
equalsGen x = pure Equals
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

existsGen :: IsMeta a => a -> Gen (Exists a Variable UnifiedPattern)
existsGen x = existsForallGen x Exists

floorGen :: IsMeta a => a -> Gen (Floor a UnifiedPattern)
floorGen x = ceilFloorGen x Floor

forallGen :: IsMeta a => a -> Gen (Forall a Variable UnifiedPattern)
forallGen x = existsForallGen x Forall

iffGen :: IsMeta a => a -> Gen (Iff a UnifiedPattern)
iffGen x = binaryOperatorGen x Iff

impliesGen :: IsMeta a => a -> Gen (Implies a UnifiedPattern)
impliesGen x = binaryOperatorGen x Implies

inGen :: IsMeta a => a -> Gen (In a UnifiedPattern)
inGen x = pure In
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) unifiedPatternGen

nextGen :: IsMeta a => a -> Gen (Next a UnifiedPattern)
nextGen x = pure Next
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

notGen :: IsMeta a => a -> Gen (Not a UnifiedPattern)
notGen x = pure Not
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) unifiedPatternGen

orGen :: IsMeta a => a -> Gen (Or a UnifiedPattern)
orGen x = binaryOperatorGen x Or

rewritesGen :: IsMeta a => a -> Gen (Rewrites a UnifiedPattern)
rewritesGen x = binaryOperatorGen x Rewrites

topGen :: IsMeta a => a -> Gen (Top a UnifiedPattern)
topGen x = topBottomGen x Top

patternGen :: IsMeta a => a -> Gen (Pattern a Variable UnifiedPattern)
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
        , InPattern <$> inGen x
        , NextPattern <$> nextGen Object
        , NotPattern <$> notGen x
        , OrPattern <$> orGen x
        , RewritesPattern <$> rewritesGen Object
        , StringLiteralPattern <$> stringLiteralGen
        , CharLiteralPattern <$> charLiteralGen
        , TopPattern <$> topGen x
        , VariablePattern <$> variableGen x
        ]
    ) checkMetaObject
  where
    checkMetaObject (StringLiteralPattern _) = koreLevel x == MetaLevel
    checkMetaObject (CharLiteralPattern _)   = koreLevel x == MetaLevel
    checkMetaObject (NextPattern _)          = koreLevel x == ObjectLevel
    checkMetaObject (RewritesPattern _)      = koreLevel x == ObjectLevel
    checkMetaObject _                        = True

unifiedPatternGen :: Gen UnifiedPattern
unifiedPatternGen = sized (\n ->
    if n<=0
        then oneof
            [ MetaPattern . StringLiteralPattern <$> stringLiteralGen
            , MetaPattern . CharLiteralPattern <$> charLiteralGen
            ]
        else oneof
            [ MetaPattern <$> patternGen Meta
            , ObjectPattern <$> patternGen Object
            ]
    )

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

sentenceImportGen :: Gen SentenceImport
sentenceImportGen = pure SentenceImport
    <*> scale (`div` 2) moduleNameGen
    <*> scale (`div` 2) attributesGen

sentenceAxiomGen :: Gen SentenceAxiom
sentenceAxiomGen = pure SentenceAxiom
    <*> couple (scale (`div` 2) unifiedSortVariableGen)
    <*> scale (`div` 2) unifiedPatternGen
    <*> scale (`div` 2) attributesGen

sentenceSortGen :: Gen SentenceSort
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
