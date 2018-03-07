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
stringLiteralGen = StringLiteral <$> listOf ( suchThat (oneof
    [ chooseAny
    , elements "\a\b\f\n\r\t\v\\\""
    , choose ('\32','\127')
    , choose ('\0','\255')
    , choose ('\0','\65535')
    ])
    (/='?'))

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

unaryOperatorGen
    :: IsMeta a
    => Gen child
    -> a
    -> (Sort a -> child -> b a child)
    -> Gen (b a child)
unaryOperatorGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) childGen

binaryOperatorGen
    :: IsMeta a
    => Gen child
    -> a
    -> (Sort a -> child -> child -> b a child)
    -> Gen (b a child)
binaryOperatorGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) childGen
    <*> scale (`div` 2) childGen

ceilFloorGen
    :: IsMeta a
    => Gen child
    -> a
    -> (Sort a -> Sort a -> child -> c a child)
    -> Gen (c a child)
ceilFloorGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) childGen

equalsInGen
    :: IsMeta a
    => Gen child
    -> a
    -> (Sort a -> Sort a -> child -> child -> c a child)
    -> Gen (c a child)
equalsInGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) childGen
    <*> scale (`div` 2) childGen

existsForallGen
    :: IsMeta a
    => Gen child
    -> a
    -> (Sort a -> Variable a -> child -> q a Variable child)
    -> Gen (q a Variable child)
existsForallGen childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (variableGen x)
    <*> scale (`div` 2) childGen

topBottomGen
    :: IsMeta a
    => a
    -> (Sort a -> t a child)
    -> Gen (t a child)
topBottomGen x constructor = pure constructor
    <*> sortGen x

andGen :: IsMeta a => Gen child -> a -> Gen (And a child)
andGen childGen x = binaryOperatorGen childGen x And

applicationGen
    :: IsMeta a
    => Gen child
    -> a
    -> Gen (Application a child)
applicationGen childGen x = pure Application
    <*> scale (`div` 2) (symbolOrAliasGen x)
    <*> couple (scale (`div` 4) childGen)

bottomGen :: IsMeta a => a -> Gen (Bottom a child)
bottomGen x = topBottomGen x Bottom

ceilGen :: IsMeta a => Gen child -> a -> Gen (Ceil a child)
ceilGen childGen x = ceilFloorGen childGen x Ceil

equalsGen
    :: IsMeta a => Gen child -> a -> Gen (Equals a child)
equalsGen childGen x = equalsInGen childGen x Equals

existsGen
    :: IsMeta a
    => Gen child
    -> a
    -> Gen (Exists a Variable child)
existsGen childGen x = existsForallGen childGen x Exists

floorGen :: IsMeta a => Gen child -> a -> Gen (Floor a child)
floorGen childGen x = ceilFloorGen childGen x Floor

forallGen :: IsMeta a => Gen child -> a -> Gen (Forall a Variable child)
forallGen childGen x = existsForallGen childGen x Forall

iffGen :: IsMeta a => Gen child -> a -> Gen (Iff a child)
iffGen childGen x = binaryOperatorGen childGen x Iff

impliesGen :: IsMeta a => Gen child -> a -> Gen (Implies a child)
impliesGen childGen x = binaryOperatorGen childGen x Implies

inGen :: IsMeta a => Gen child -> a -> Gen (In a child)
inGen childGen x = equalsInGen childGen x In

nextGen :: IsMeta a => Gen child -> a -> Gen (Next a child)
nextGen childGen x = unaryOperatorGen childGen x Next

notGen :: IsMeta a => Gen child -> a -> Gen (Not a child)
notGen childGen x = unaryOperatorGen childGen x Not

orGen :: IsMeta a => Gen child -> a -> Gen (Or a child)
orGen childGen x = binaryOperatorGen childGen x Or

rewritesGen :: IsMeta a => Gen child -> a -> Gen (Rewrites a child)
rewritesGen childGen x = binaryOperatorGen childGen x Rewrites

topGen :: IsMeta a => a -> Gen (Top a child)
topGen x = topBottomGen x Top

patternGen :: IsMeta a => Gen child -> a -> Gen (Pattern a Variable child)
patternGen childGen x =
    suchThat ( oneof
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
        , NextPattern <$> nextGen childGen Object
        , NotPattern <$> notGen childGen x
        , OrPattern <$> orGen childGen x
        , RewritesPattern <$> rewritesGen childGen Object
        , StringLiteralPattern <$> stringLiteralGen
        , TopPattern <$> topGen x
        , VariablePattern <$> variableGen x
        ]
    ) checkMetaObject
  where
    checkMetaObject (StringLiteralPattern _) = koreLevel x == MetaLevel
    checkMetaObject (NextPattern _)          = koreLevel x == ObjectLevel
    checkMetaObject (RewritesPattern _)      = koreLevel x == ObjectLevel
    checkMetaObject _                        = True

unifiedPatternGen :: Gen UnifiedPattern
unifiedPatternGen = sized (\n ->
    if n<=0
        then MetaPattern . StringLiteralPattern <$> stringLiteralGen
        else oneof
            [ MetaPattern <$> patternGen unifiedPatternGen Meta
            , ObjectPattern <$> patternGen unifiedPatternGen Object
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
