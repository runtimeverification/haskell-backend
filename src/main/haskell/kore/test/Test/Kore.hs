module Test.Kore where

import Test.QuickCheck.Gen
       ( Gen, choose, chooseAny, elements, frequency, getSize, listOf, oneof,
       scale, sized, suchThat, vectorOf )
import Test.QuickCheck.Instances ()

import           Data.Functor.Foldable
import           Data.Proxy
import           Data.Reflection
                 ( Given )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
import           Kore.MetaML.AST
import           Kore.Parser.LexemeImpl
import           Kore.Predicate.Predicate
import           Kore.Step.Pattern

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
genericIdGen :: [Char] -> [Char] -> Gen Text
genericIdGen firstChars nextChars = do
    firstChar <- elements firstChars
    body <- listOf (elements nextChars)
    (return . Text.pack) (firstChar : body)

idGen :: MetaOrObject level => level -> Gen (Id level)
idGen x
    | isObject x = testId <$> objectId
    | otherwise  = testId . (Text.cons '#') <$> objectId
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
    | otherwise = SortActual <$> elements metaSortIds <*> pure []
  where
    metaSortIds = testId . Text.pack . show <$> metaSortsList

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

variableGen
    :: MetaOrObject level
    => [Variable level]
    -> level
    -> Gen (Variable level)
variableGen vars x = oneof (newVar : map (elements . pure) vars)
  where
    newVar = pure Variable
        <*> scale (`div` 2) (idGen x)
        <*> scale (`div` 2) (sortGen x)

unifiedVariableGen :: Gen (Unified Variable)
unifiedVariableGen = scale (`div` 2) $ oneof
    [ UnifiedObject <$> variableGen [] Object
    , UnifiedMeta <$> variableGen [] Meta
    ]

unaryOperatorGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> (Sort level -> child -> b level child)
    -> Gen (b level child)
unaryOperatorGen vars childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (childGen vars)

binaryOperatorGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> (Sort level -> child -> child -> b level child)
    -> Gen (b level child)
binaryOperatorGen vars childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (childGen vars)
    <*> scale (`div` 2) (childGen vars)

ceilFloorGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> (Sort level -> Sort level -> child -> c level child)
    -> Gen (c level child)
ceilFloorGen vars childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (childGen vars)

equalsInGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> (Sort level -> Sort level -> child -> child -> c level child)
    -> Gen (c level child)
equalsInGen vars childGen x constructor = pure constructor
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (childGen vars)
    <*> scale (`div` 2) (childGen vars)

existsForallGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> (Sort level -> Variable level -> child -> q level Variable child)
    -> Gen (q level Variable child)
existsForallGen vars childGen x constructor = do
    sort <- scale (`div` 2) (sortGen x)
    var <- scale (`div` 2) (variableGen vars x)
    child <- scale (`div` 2) (childGen (var : vars))
    pure $ constructor sort var child

topBottomGen
    :: MetaOrObject level
    => [Variable level]
    -> level
    -> (Sort level -> t level child)
    -> Gen (t level child)
topBottomGen _vars x constructor = pure constructor
    <*> sortGen x

andGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (And level child)
andGen vars childGen x = binaryOperatorGen vars childGen x And

applicationGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Application level child)
applicationGen vars childGen x = pure Application
    <*> scale (`div` 2) (symbolOrAliasGen x)
    <*> couple (scale (`div` 4) (childGen vars))

bottomGen
    :: MetaOrObject level
    => [Variable level]
    -> level
    -> Gen (Bottom level child)
bottomGen vars x = topBottomGen vars x Bottom

ceilGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Ceil level child)
ceilGen vars childGen x = ceilFloorGen vars childGen x Ceil

equalsGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Equals level child)
equalsGen vars childGen x = equalsInGen vars childGen x Equals

domainValueGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen (dom child))
    -> level
    -> Gen (DomainValue level dom child)
domainValueGen vars childGen level =
    DomainValue
        <$> scale (`div` 2) (sortGen level)
        <*> childGen vars

externalDomainGen :: [Variable level] -> Gen (Domain.Builtin child)
externalDomainGen _ =
    Domain.BuiltinPattern . StringLiteral_ . getStringLiteral
        <$> stringLiteralGen

builtinDomainGen
    :: ([Variable level] -> Gen child)
    -> [Variable level]
    -> Gen (Domain.Builtin child)
builtinDomainGen _ _ =
    Domain.BuiltinPattern . StringLiteral_ . getStringLiteral
        <$> stringLiteralGen

existsGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Exists level Variable child)
existsGen vars childGen x = existsForallGen vars childGen x Exists

floorGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Floor level child)
floorGen vars childGen x = ceilFloorGen vars childGen x Floor

forallGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Forall level Variable child)
forallGen vars childGen x = existsForallGen vars childGen x Forall

iffGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Iff level child)
iffGen vars childGen x = binaryOperatorGen vars childGen x Iff

impliesGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Implies level child)
impliesGen vars childGen x = binaryOperatorGen vars childGen x Implies

inGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (In level child)
inGen vars childGen x = equalsInGen vars childGen x In

nextGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Next level child)
nextGen vars childGen x = unaryOperatorGen vars childGen x Next

notGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Not level child)
notGen vars childGen x = unaryOperatorGen vars childGen x Not

orGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Or level child)
orGen vars childGen x = binaryOperatorGen vars childGen x Or

rewritesGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Rewrites level child)
rewritesGen vars childGen x = binaryOperatorGen vars childGen x Rewrites

topGen
    :: MetaOrObject level
    => [Variable level]
    -> level
    -> Gen (Top level child)
topGen vars  x = topBottomGen vars x Top

patternGen
    :: MetaOrObject level
    => [Variable level]
    -> ([Variable level] -> Gen child)
    -> level
    -> Gen (Pattern level dom Variable child)
patternGen vars childGen x =
    frequency
        [ (1, AndPattern <$> andGen vars childGen x)
        , (1, ApplicationPattern <$> applicationGen vars childGen x)
        , (1, BottomPattern <$> bottomGen vars x)
        , (1, CeilPattern <$> ceilGen vars childGen x)
        , (1, EqualsPattern <$> equalsGen vars childGen x)
        , (1, ExistsPattern <$> existsGen vars childGen x)
        , (1, FloorPattern <$> floorGen vars childGen x)
        , (1, ForallPattern <$> forallGen vars childGen x)
        , (1, IffPattern <$> iffGen vars childGen x)
        , (1, ImpliesPattern <$> impliesGen vars childGen x)
        , (1, InPattern <$> inGen vars childGen x)
        , (1, NotPattern <$> notGen vars childGen x)
        , (1, OrPattern <$> orGen vars childGen x)
        , (1, TopPattern <$> topGen vars x)
        , (5, VariablePattern <$> variableGen vars x)
        ]

purePatternGen
    :: forall level. MetaOrObject level
    => level
    -> Gen (CommonPurePattern level Domain.Builtin ())
purePatternGen level =
    childGen []
  where
    childGen vars = embed . (mempty :<) <$> sized (purePatternGenWorker vars)
    purePatternGenWorker vars n
      | n <= 0 =
        case isMetaOrObject (Proxy :: Proxy level) of
            IsMeta ->
                oneof
                    [ StringLiteralPattern <$> stringLiteralGen
                    , CharLiteralPattern <$> charLiteralGen
                    ]
            IsObject ->
                oneof
                    [ DomainValuePattern
                        <$> domainValueGen vars externalDomainGen level
                    ]
      | otherwise = patternGen vars childGen level

stepPatternGen
    :: forall level. MetaOrObject level
    => level
    -> Gen (CommonStepPattern level)
stepPatternGen level =
    childGen []
  where
    childGen vars = embed . (mempty :<) <$> sized (stepPatternGenWorker vars)
    stepPatternGenWorker vars n
      | n <= 0 =
        case isMetaOrObject (Proxy :: Proxy level) of
            IsMeta ->
                oneof
                    [ StringLiteralPattern <$> stringLiteralGen
                    , CharLiteralPattern <$> charLiteralGen
                    ]
            IsObject ->
                oneof
                    [ DomainValuePattern <$> domainValueGen
                        vars
                        (builtinDomainGen childGen)
                        level
                    ]
      | otherwise = patternGen vars childGen level

korePatternGen :: Gen CommonKorePattern
korePatternGen = sized (\n ->
    if n<=0
        then oneof
            [ korePatternGenStringLiteral
            , korePatternGenCharLiteral
            ]
        else frequency
            [ (15, korePatternGenLevel Meta)
            , (15, korePatternGenLevel Object)
            , (1, korePatternGenStringLiteral)
            , (1, korePatternGenCharLiteral)
            , (1, korePatternGenDomainValue)
            , (1, korePatternGenNext)
            , (1, korePatternGenRewrites)
            ]
    )
  where
    korePatternGenLevel level =
        asCommonKorePattern <$> patternGen [] (const korePatternGen) level
    korePatternGenStringLiteral =
        asCommonKorePattern . StringLiteralPattern <$> stringLiteralGen
    korePatternGenCharLiteral =
        asCommonKorePattern . CharLiteralPattern <$> charLiteralGen
    korePatternGenDomainValue =
        asCommonKorePattern . DomainValuePattern
            <$> domainValueGen [] externalDomainGen Object
    korePatternGenNext =
        asCommonKorePattern . NextPattern
            <$> nextGen [] (const korePatternGen) Object
    korePatternGenRewrites =
        asCommonKorePattern . RewritesPattern
            <$> rewritesGen [] (const korePatternGen) Object

predicateGen
    ::  ( Given (SymbolOrAliasSorts level)
        , MetaOrObject level
        )
    => level
    -> Gen (Predicate level Variable)
predicateGen level =
    oneof
        [ makeAndPredicate <$> predicateGen level <*> predicateGen level
        , makeCeilPredicate <$> stepPatternGen level
        , makeEqualsPredicate <$> stepPatternGen level <*> stepPatternGen level
        , makeExistsPredicate <$> variableGen [] level <*> predicateGen level
        , makeForallPredicate <$> variableGen [] level <*> predicateGen level
        , pure makeFalsePredicate
        , makeFloorPredicate <$> stepPatternGen level
        , makeIffPredicate <$> predicateGen level <*> predicateGen level
        , makeImpliesPredicate <$> predicateGen level <*> predicateGen level
        , makeInPredicate <$> stepPatternGen level <*> stepPatternGen level
        , makeNotPredicate <$> predicateGen level
        , makeOrPredicate <$> predicateGen level <*> predicateGen level
        , pure makeTruePredicate
        ]

sentenceAliasGen
    :: MetaOrObject level
    => level
    -> Gen (pat dom Variable ())
    -> Gen (SentenceAlias level pat dom Variable)
sentenceAliasGen x patGen = pure SentenceAlias
    <*> scale (`div` 2) (aliasGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) (patternGen [] (const patGen) x)
    <*> scale (`div` 2) (patternGen [] (const patGen) x)
    <*> scale (`div` 2) attributesGen

sentenceSymbolGen
    :: MetaOrObject level
    => level
    -> Gen (SentenceSymbol level pat dom variable)
sentenceSymbolGen x = pure SentenceSymbol
    <*> scale (`div` 2) (symbolGen x)
    <*> couple (scale (`div` 2) (sortGen x))
    <*> scale (`div` 2) (sortGen x)
    <*> scale (`div` 2) attributesGen

sentenceImportGen
    :: Gen (SentenceImport pat dom variable)
sentenceImportGen = pure SentenceImport
    <*> scale (`div` 2) moduleNameGen
    <*> scale (`div` 2) attributesGen

sentenceAxiomGen
   :: Gen sortParam
   -> Gen (pat dom var ())
   -> Gen (SentenceAxiom sortParam pat dom var)
sentenceAxiomGen sortParamGen patGen =
    pure SentenceAxiom
        <*> couple (scale (`div` 2) sortParamGen)
        <*> scale (`div` 2) patGen
        <*> scale (`div` 2) attributesGen

sentenceSortGen
    :: MetaOrObject level
    => level -> Gen (SentenceSort level pat dom var)
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
    , asKoreAxiomSentence
        <$> sentenceAxiomGen unifiedSortVariableGen korePatternGen
    , asKoreClaimSentence
        <$> sentenceAxiomGen unifiedSortVariableGen korePatternGen
    , constructUnifiedSentence SentenceSortSentence
        <$> sentenceSortGen Object
    , constructUnifiedSentence (SentenceHookSentence . SentenceHookedSort)
        <$> sentenceSortGen Object
    , constructUnifiedSentence (SentenceHookSentence . SentenceHookedSymbol)
        <$> sentenceSymbolGen Object
    ]

moduleGen
    :: Gen (sentence sortParam pat dom variable)
    -> Gen (Module sentence sortParam pat dom variable)
moduleGen senGen = pure Module
    <*> scale (`div` 2) moduleNameGen
    <*> couple (scale (`div` 2) senGen)
    <*> scale (`div` 2) attributesGen

modulesGen
    :: Gen (sentence sortParam pat dom variable)
    -> Gen [Module sentence sortParam pat dom variable]
modulesGen senGen = couple1 (scale (`div` 2) (moduleGen senGen))

definitionGen
    :: Gen (sentence sortParam pat dom variable)
    -> Gen (Definition sentence sortParam pat dom variable)
definitionGen senGen = pure Definition
    <*> scale (`div` 2) attributesGen
    <*> scale (`div` 2) (modulesGen senGen)

metaMLPatternGen :: Gen (MetaMLPattern Variable ())
metaMLPatternGen = asPurePattern . (mempty :<) <$> sized metaMLPatternGenWorker
  where
    metaMLPatternGenWorker n
      | n <= 0 =
        oneof
            [ StringLiteralPattern <$> stringLiteralGen
            , CharLiteralPattern <$> charLiteralGen
            ]
      | otherwise =
        frequency
            [ (15, patternGen [] (const metaMLPatternGen) Meta)
            , (1, StringLiteralPattern <$> stringLiteralGen)
            , (1, CharLiteralPattern <$> charLiteralGen)
            ]

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

testId :: Text -> Id level
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }

sortVariable :: Text -> SortVariable level
sortVariable name =
    SortVariable { getSortVariable = testId name }

sortVariableSort :: Text -> Sort level
sortVariableSort name =
    SortVariableSort (sortVariable name)

sortActual :: Text -> [Sort level] -> Sort level
sortActual name sorts =
    SortActualSort SortActual
        { sortActualName = testId name
        , sortActualSorts = sorts
        }
