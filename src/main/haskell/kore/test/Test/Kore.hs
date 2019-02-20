module Test.Kore
    ( testId
    , standaloneGen
    , idGen
    , stringLiteralGen
    , charLiteralGen
    , symbolGen
    , aliasGen
    , sortVariableGen
    , sortGen
    , unifiedVariableGen
    , unifiedSortGen
    , korePatternGen
    , attributesGen
    , koreSentenceGen
    , moduleGen
    , definitionGen
    , sortActual
    , sortVariable
    , sortVariableSort
    , stepPatternGen
    , metaMLPatternGen
    , expandedPatternGen
    , orOfExpandedPatternGen
    , predicateGen
    , predicateChildGen
    , metaModuleGen
    , variableGen
    , Logger.emptyLogger
    ) where

import           Hedgehog
                 ( MonadGen )
import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import           Control.Monad.Reader
                 ( ReaderT )
import qualified Control.Monad.Reader as Reader
import           Data.Proxy
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import           Kore.Implicit.ImplicitSorts
import qualified Kore.Logger.Output as Logger
                 ( emptyLogger )
import           Kore.MetaML.AST
import           Kore.Parser.Lexeme
import           Kore.Predicate.Predicate
import           Kore.Step.ExpandedPattern
import           Kore.Step.OrOfExpandedPattern
import           Kore.Step.Pattern

{- | @Context@ stores the variables and sort variables in scope.
 -}
data Context =
    Context
        { objectVariables :: ![Variable Object]
        , metaVariables :: ![Variable Meta]
        , objectSortVariables :: ![SortVariable Object]
        , metaSortVariables :: ![SortVariable Meta]
        }

emptyContext :: Context
emptyContext =
    Context
        { objectVariables = []
        , metaVariables = []
        , objectSortVariables = []
        , metaSortVariables = []
        }

standaloneGen :: Gen a -> Hedgehog.Gen a
standaloneGen generator =
    Reader.runReaderT generator emptyContext

addVariable
    :: MetaOrObject level
    => Variable level
    -> Context
    -> Context
addVariable var =
    case isMetaOrObject var of
        IsMeta -> \ctx@Context { metaVariables } ->
            ctx { metaVariables = var : metaVariables }
        IsObject -> \ctx@Context { objectVariables } ->
            ctx { objectVariables = var : objectVariables }

addVariables
    :: MetaOrObject level
    => [Variable level]
    -> Context
    -> Context
addVariables vars = \ctx -> foldr addVariable ctx vars

addSortVariable
    ::  forall level.
        MetaOrObject level
    => SortVariable level
    -> Context
    -> Context
addSortVariable var =
    case isMetaOrObject var of
        IsMeta -> \ctx@Context { metaSortVariables } ->
            ctx { metaSortVariables = var : metaSortVariables }
        IsObject -> \ctx@Context { objectSortVariables } ->
            ctx { objectSortVariables = var : objectSortVariables }

addSortVariables
    ::  forall level.
        MetaOrObject level
    => [SortVariable level]
    -> Context
    -> Context
addSortVariables vars = \ctx -> foldr addSortVariable ctx vars

addUnifiedSortVariable
    :: Unified SortVariable
    -> Context
    -> Context
addUnifiedSortVariable =
    \case
        UnifiedMeta var -> addSortVariable var
        UnifiedObject var -> addSortVariable var

addUnifiedSortVariables
    :: [Unified SortVariable]
    -> Context
    -> Context
addUnifiedSortVariables vars = \ctx -> foldr addUnifiedSortVariable ctx vars

type Gen = ReaderT Context Hedgehog.Gen

couple :: MonadGen m => m a -> m [a]
couple = Gen.list (Range.linear 0 3)

couple1 :: MonadGen m => m a -> m [a]
couple1 = Gen.list (Range.linear 1 3)

{-# ANN genericIdGen ("HLint: ignore Use String" :: String) #-}
genericIdGen :: MonadGen m => m Char -> m Char -> m Text
genericIdGen firstChar nextChar = do
    chars <-
        (:)
            <$> firstChar
            <*> Gen.list (Range.linear 0 32) nextChar
    return (Text.pack chars)

idGen :: MonadGen m => IsMetaOrObject level -> m (Id level)
idGen =
    \case
        IsObject -> testId <$> objectIdGen
        IsMeta -> testId . (Text.cons '#') <$> objectIdGen

objectIdGen :: MonadGen m => m Text
objectIdGen =
    genericIdGen
        (Gen.element idFirstChars)
        (Gen.element $ idFirstChars ++ idOtherChars)

stringLiteralGen :: MonadGen m => m StringLiteral
stringLiteralGen = StringLiteral <$> Gen.text (Range.linear 0 256) charGen

charLiteralGen :: MonadGen m => m CharLiteral
charLiteralGen = CharLiteral <$> charGen

charGen :: MonadGen m => m Char
charGen =
    Gen.choice
        [ Gen.ascii
        , Gen.enum '\x80' '\xFF'
        , Gen.enum '\x100' '\xD7FF'
        , Gen.enum '\xE000' '\x10FFFF'
        ]

symbolOrAliasRawGen
    :: MetaOrObject level
    => (Id level -> [Sort level] -> s level)
    -> Gen (s level)
symbolOrAliasRawGen constructor =
    constructor
        <$> Gen.small (idGen level)
        <*> couple (Gen.small sortGen)
  where
    level = isMetaOrObject Proxy

symbolOrAliasDeclarationRawGen
    :: (MetaOrObject level, MonadGen m)
    => (Id level -> [SortVariable level] -> s level)
    -> m (s level)
symbolOrAliasDeclarationRawGen constructor =
    constructor
        <$> Gen.small (idGen level)
        <*> couple (Gen.small sortVariableGen)
  where
    level = isMetaOrObject Proxy

symbolOrAliasGen :: MetaOrObject level => Gen (SymbolOrAlias level)
symbolOrAliasGen = symbolOrAliasRawGen SymbolOrAlias

symbolGen :: (MetaOrObject level, MonadGen m) => m (Symbol level)
symbolGen = symbolOrAliasDeclarationRawGen Symbol

aliasGen :: (MetaOrObject level, MonadGen m) => m (Alias level)
aliasGen = symbolOrAliasDeclarationRawGen Alias

sortVariableGen :: (MetaOrObject level, MonadGen m) => m (SortVariable level)
sortVariableGen = SortVariable <$> idGen (isMetaOrObject Proxy)

sortActualGen :: IsMetaOrObject level -> Gen (SortActual level)
sortActualGen =
    \case
        IsObject ->
            SortActual
                <$> Gen.small (idGen IsObject)
                <*> couple (Gen.small sortGen)
        IsMeta ->
            SortActual
                <$> Gen.element metaSortIds
                <*> pure []
  where
    metaSortIds = testId . Text.pack . show <$> metaSortsList

sortGen :: forall level. MetaOrObject level => Gen (Sort level)
sortGen =
    case level of
        IsObject -> do
            Context { objectSortVariables } <- Reader.ask
            sortGenWorker objectSortVariables
        IsMeta -> do
            Context { metaSortVariables } <- Reader.ask
            sortGenWorker metaSortVariables
  where
    level = isMetaOrObject (Proxy @level)
    sortGenWorker :: [SortVariable level] -> Gen (Sort level)
    sortGenWorker =
        \case
            [] -> actualSort
            sortVariables ->
                Gen.choice
                    [ SortVariableSort <$> Gen.element sortVariables
                    , actualSort
                    ]
      where
        actualSort = SortActualSort <$> sortActualGen level

unifiedSortGen :: Gen (Unified Sort)
unifiedSortGen =
    Gen.choice
        [ UnifiedObject <$> sortGen
        , UnifiedMeta <$> sortGen
        ]

unifiedSortVariableGen :: Gen UnifiedSortVariable
unifiedSortVariableGen =
    Gen.choice
        [ UnifiedObject <$> sortVariableGen
        , UnifiedMeta <$> sortVariableGen
        ]

moduleNameGen :: MonadGen m => m ModuleName
moduleNameGen = ModuleName <$> objectIdGen

variableGen
    ::  forall level.
        MetaOrObject level
    => Sort level
    -> Gen (Variable level)
variableGen patternSort =
    case level of
        IsMeta -> do
            Context { metaVariables } <- Reader.ask
            variableGenWorker metaVariables
        IsObject -> do
            Context { objectVariables } <- Reader.ask
            variableGenWorker objectVariables
  where
    level = isMetaOrObject patternSort
    bySort Variable { variableSort } = variableSort == patternSort
    variableGenWorker :: [Variable level] -> Gen (Variable level)
    variableGenWorker variables =
        case filter bySort variables of
            [] -> freshVariable
            variables' ->
                Gen.choice
                    [ Gen.element variables'
                    , freshVariable
                    ]
      where
        freshVariable =
            Variable <$> idGen level <*> pure mempty <*> pure patternSort

unifiedVariableGen :: Unified Sort -> Gen (Unified Variable)
unifiedVariableGen = transformUnified unifiedVariableGenWorker
  where
    unifiedVariableGenWorker sort =
        asUnified <$> variableGen sort

unaryOperatorGen
    :: MonadGen m
    => (Sort level -> child -> b level child)
    -> (Sort level -> m child)
    -> Sort level
    -> m (b level child)
unaryOperatorGen constructor childGen patternSort =
    constructor patternSort <$> Gen.small (childGen patternSort)

binaryOperatorGen
    :: (Sort level -> child -> child -> b level child)
    -> (Sort level -> Gen child)
    -> Sort level
    -> Gen (b level child)
binaryOperatorGen constructor childGen patternSort =
    constructor patternSort
        <$> Gen.small (childGen patternSort)
        <*> Gen.small (childGen patternSort)

ceilFloorGen
    :: MetaOrObject level
    => (Sort level -> Sort level -> child -> c level child)
    -> (Sort level -> Gen child)
    -> Sort level
    -> Gen (c level child)
ceilFloorGen constructor childGen resultSort = do
    operandSort <- Gen.small sortGen
    constructor resultSort operandSort <$> Gen.small (childGen operandSort)

equalsInGen
    :: MetaOrObject level
    => (Sort level -> Sort level -> child -> child -> c level child)
    -> (Sort level -> Gen child)
    -> Sort level
    -> Gen (c level child)
equalsInGen constructor childGen resultSort = do
    operandSort <- Gen.small sortGen
    constructor resultSort operandSort
        <$> Gen.small (childGen operandSort)
        <*> Gen.small (childGen operandSort)

existsForallGen
    :: MetaOrObject level
    => (Sort level -> Variable level -> child -> q level Variable child)
    -> (Sort level -> Gen child)
    -> Sort level
    -> Gen (q level Variable child)
existsForallGen constructor childGen patternSort = do
    varSort <- Gen.small sortGen
    var <- Gen.small (variableGen varSort)
    constructor patternSort var
        <$> Gen.small (Reader.local (addVariable var) $ childGen patternSort)

topBottomGen
    :: (Sort level -> t level child)
    -> Sort level
    -> Gen (t level child)
topBottomGen constructor = pure . constructor

andGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (And level child)
andGen = binaryOperatorGen And

applicationGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Application level child)
applicationGen childGen _ =
    Application
        <$> Gen.small symbolOrAliasGen
        <*> couple (Gen.small (childGen =<< sortGen))

bottomGen :: Sort level -> Gen (Bottom level child)
bottomGen = topBottomGen Bottom

ceilGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Ceil level child)
ceilGen = ceilFloorGen Ceil

equalsGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Equals level child)
equalsGen = equalsInGen Equals

domainValueGen
    :: (Sort level -> Gen (domain child))
    -> Sort level
    -> Gen (DomainValue level domain child)
domainValueGen childGen domainValueSort = do
    domainValueChild <- childGen domainValueSort
    return DomainValue { domainValueSort, domainValueChild }

externalDomainGen :: Sort Object -> Gen (Domain.Builtin child)
externalDomainGen _ =
    Domain.BuiltinPattern
        . Kore.AST.Pure.eraseAnnotations
        . mkStringLiteral
        . getStringLiteral
        <$> stringLiteralGen

builtinDomainGen :: Sort Object -> Gen (Domain.Builtin child)
builtinDomainGen _ = Gen.choice
    [ Domain.BuiltinPattern
        . Kore.AST.Pure.eraseAnnotations
        . mkStringLiteral
        . getStringLiteral
        <$> stringLiteralGen
    , Domain.BuiltinInteger <$> genInteger
    , Domain.BuiltinBool <$> Gen.bool
    ]
  where
    genInteger = Gen.integral (Range.linear (-1024) 1024)

existsGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Exists level Variable child)
existsGen = existsForallGen Exists

floorGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Floor level child)
floorGen = ceilFloorGen Floor

forallGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Forall level Variable child)
forallGen = existsForallGen Forall

iffGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Iff level child)
iffGen = binaryOperatorGen Iff

impliesGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Implies level child)
impliesGen = binaryOperatorGen Implies

inGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (In level child)
inGen = equalsInGen In

nextGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Next level child)
nextGen = unaryOperatorGen Next

notGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Not level child)
notGen = unaryOperatorGen Not

orGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Or level child)
orGen = binaryOperatorGen Or

rewritesGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Rewrites level child)
rewritesGen = binaryOperatorGen Rewrites

topGen :: Sort level -> Gen (Top level child)
topGen = topBottomGen Top

patternGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Pattern level dom Variable child)
patternGen childGen patternSort =
    Gen.frequency
        [ (1, AndPattern <$> andGen childGen patternSort)
        , (1, ApplicationPattern <$> applicationGen childGen patternSort)
        , (1, BottomPattern <$> bottomGen patternSort)
        , (1, CeilPattern <$> ceilGen childGen patternSort)
        , (1, EqualsPattern <$> equalsGen childGen patternSort)
        , (1, ExistsPattern <$> existsGen childGen patternSort)
        , (1, FloorPattern <$> floorGen childGen patternSort)
        , (1, ForallPattern <$> forallGen childGen patternSort)
        , (1, IffPattern <$> iffGen childGen patternSort)
        , (1, ImpliesPattern <$> impliesGen childGen patternSort)
        , (1, InPattern <$> inGen childGen patternSort)
        , (1, NotPattern <$> notGen childGen patternSort)
        , (1, OrPattern <$> orGen childGen patternSort)
        , (1, TopPattern <$> topGen patternSort)
        , (5, VariablePattern <$> variableGen patternSort)
        ]

stepPatternGen
    :: MetaOrObject level
    => Hedgehog.Gen (CommonStepPattern level)
stepPatternGen = standaloneGen (stepPatternChildGen =<< sortGen)

stepPatternChildGen
    :: MetaOrObject level
    => Sort level
    -> Gen (CommonStepPattern level)
stepPatternChildGen patternSort =
    Gen.sized stepPatternChildGenWorker
  where
    stepPatternChildGenWorker n
      | n <= 1 =
        case isMetaOrObject patternSort of
            IsMeta
              | patternSort == stringMetaSort ->
                mkStringLiteral . getStringLiteral <$> stringLiteralGen
              | patternSort == charMetaSort ->
                mkCharLiteral . getCharLiteral <$> charLiteralGen
              | otherwise ->
                mkVar <$> variableGen patternSort
            IsObject ->
                mkDomainValue patternSort <$> builtinDomainGen patternSort
      | otherwise =
        (Gen.small . Gen.frequency)
            [ (1, stepPatternAndGen)
            , (1, stepPatternAppGen)
            , (1, stepPatternBottomGen)
            , (1, stepPatternCeilGen)
            , (1, stepPatternEqualsGen)
            , (1, stepPatternExistsGen)
            , (1, stepPatternFloorGen)
            , (1, stepPatternForallGen)
            , (1, stepPatternIffGen)
            , (1, stepPatternImpliesGen)
            , (1, stepPatternInGen)
            , (1, stepPatternNotGen)
            , (1, stepPatternOrGen)
            , (1, stepPatternTopGen)
            , (5, stepPatternVariableGen)
            ]
    stepPatternAndGen =
        mkAnd
            <$> stepPatternChildGen patternSort
            <*> stepPatternChildGen patternSort
    stepPatternAppGen =
        mkApp patternSort
            <$> symbolOrAliasGen
            <*> couple (stepPatternChildGen =<< sortGen)
    stepPatternBottomGen = pure (mkBottom patternSort)
    stepPatternCeilGen = do
        child <- stepPatternChildGen =<< sortGen
        pure (mkCeil patternSort child)
    stepPatternEqualsGen = do
        operandSort <- sortGen
        mkEquals patternSort
            <$> stepPatternChildGen operandSort
            <*> stepPatternChildGen operandSort
    stepPatternExistsGen = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (stepPatternChildGen patternSort)
        pure (mkExists var child)
    stepPatternForallGen = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (stepPatternChildGen patternSort)
        pure (mkForall var child)
    stepPatternFloorGen = do
        child <- stepPatternChildGen =<< sortGen
        pure (mkFloor patternSort child)
    stepPatternIffGen =
        mkIff
            <$> stepPatternChildGen patternSort
            <*> stepPatternChildGen patternSort
    stepPatternImpliesGen =
        mkImplies
            <$> stepPatternChildGen patternSort
            <*> stepPatternChildGen patternSort
    stepPatternInGen =
        mkIn patternSort
            <$> stepPatternChildGen patternSort
            <*> stepPatternChildGen patternSort
    stepPatternNotGen =
        mkNot <$> stepPatternChildGen patternSort
    stepPatternOrGen =
        mkOr
            <$> stepPatternChildGen patternSort
            <*> stepPatternChildGen patternSort
    stepPatternTopGen = pure (mkTop patternSort)
    stepPatternVariableGen = mkVar <$> variableGen patternSort

korePatternGen :: Hedgehog.Gen CommonKorePattern
korePatternGen =
    standaloneGen (transformUnified korePatternChildGen =<< unifiedSortGen)

korePatternChildGen
    ::  forall level.
        MetaOrObject level
    => Sort level
    -> Gen CommonKorePattern
korePatternChildGen patternSort' =
    Gen.sized korePatternChildGenWorker
  where
    korePatternChildGenWorker n
      | n <= 1 =
        case isMetaOrObject patternSort' of
            IsMeta
              | patternSort' == stringMetaSort ->
                korePatternGenStringLiteral
              | patternSort' == charMetaSort ->
                korePatternGenCharLiteral
              | otherwise ->
                korePatternGenVariable
            IsObject ->
                korePatternGenDomainValue
      | otherwise =
        case isMetaOrObject patternSort' of
            IsMeta ->
                korePatternGenLevel
            IsObject ->
                Gen.frequency
                    [ (15, korePatternGenLevel)
                    , (1, korePatternGenNext)
                    , (1, korePatternGenRewrites)
                    ]

    korePatternGenLevel :: Gen CommonKorePattern
    korePatternGenLevel =
        asCommonKorePattern <$> patternGen korePatternChildGen patternSort'

    korePatternGenStringLiteral :: Gen CommonKorePattern
    korePatternGenStringLiteral =
        asCommonKorePattern . StringLiteralPattern <$> stringLiteralGen

    korePatternGenCharLiteral :: Gen CommonKorePattern
    korePatternGenCharLiteral =
        asCommonKorePattern . CharLiteralPattern <$> charLiteralGen

    korePatternGenDomainValue :: level ~ Object => Gen CommonKorePattern
    korePatternGenDomainValue =
        asCommonKorePattern . DomainValuePattern
            <$> domainValueGen externalDomainGen patternSort'

    korePatternGenNext :: level ~ Object => Gen CommonKorePattern
    korePatternGenNext =
        asCommonKorePattern . NextPattern
            <$> nextGen korePatternChildGen patternSort'

    korePatternGenRewrites :: level ~ Object => Gen CommonKorePattern
    korePatternGenRewrites =
        asCommonKorePattern . RewritesPattern
            <$> rewritesGen korePatternChildGen patternSort'

    korePatternGenVariable :: Gen CommonKorePattern
    korePatternGenVariable =
        asCommonKorePattern . VariablePattern <$> variableGen patternSort'

korePatternUnifiedGen :: Gen CommonKorePattern
korePatternUnifiedGen =
    transformUnified korePatternChildGen =<< unifiedSortGen

predicateGen
    :: MetaOrObject level
    => Gen (CommonStepPattern level)
    -> Hedgehog.Gen (Predicate level Variable)
predicateGen childGen = standaloneGen (predicateChildGen childGen =<< sortGen)

predicateChildGen
    :: MetaOrObject level
    => Gen (CommonStepPattern level)
    -> Sort level
    -> Gen (Predicate level Variable)
predicateChildGen childGen patternSort' =
    Gen.recursive
        Gen.choice
        -- non-recursive generators
        [ pure makeFalsePredicate
        , pure makeTruePredicate
        , predicateChildGenCeil
        , predicateChildGenEquals
        , predicateChildGenFloor
        , predicateChildGenIn
        ]
        -- recursive generators
        [ predicateChildGenAnd
        , predicateChildGenExists
        , predicateChildGenForall
        , predicateChildGenIff
        , predicateChildGenImplies
        , predicateChildGenNot
        , predicateChildGenOr
        ]
  where
    predicateChildGenAnd =
        makeAndPredicate
            <$> predicateChildGen childGen patternSort'
            <*> predicateChildGen childGen patternSort'
    predicateChildGenOr =
        makeOrPredicate
            <$> predicateChildGen childGen patternSort'
            <*> predicateChildGen childGen patternSort'
    predicateChildGenIff =
        makeIffPredicate
            <$> predicateChildGen childGen patternSort'
            <*> predicateChildGen childGen patternSort'
    predicateChildGenImplies =
        makeImpliesPredicate
            <$> predicateChildGen childGen patternSort'
            <*> predicateChildGen childGen patternSort'
    predicateChildGenCeil = makeCeilPredicate <$> childGen
    predicateChildGenFloor = makeFloorPredicate <$> childGen
    predicateChildGenEquals = makeEqualsPredicate <$> childGen <*> childGen
    predicateChildGenIn = makeInPredicate <$> childGen <*> childGen
    predicateChildGenNot = do
        makeNotPredicate <$> predicateChildGen childGen patternSort'
    predicateChildGenExists = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (predicateChildGen childGen patternSort')
        return (makeExistsPredicate var child)
    predicateChildGenForall = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (predicateChildGen childGen patternSort')
        return (makeForallPredicate var child)

sentenceAliasGen
    ::  forall level patternType.
        MetaOrObject level
    => (Sort level -> Gen patternType)
    -> Gen (SentenceAlias level patternType)
sentenceAliasGen patGen =
    Gen.small sentenceAliasGenWorker
  where
    sentenceAliasGenWorker = do
        sentenceAliasAlias <- aliasGen
        let Alias { aliasParams } = sentenceAliasAlias
        Reader.local (addSortVariables aliasParams) $ do
            sentenceAliasSorts <- couple sortGen
            sentenceAliasResultSort <- sortGen
            variables <- traverse variableGen sentenceAliasSorts
            let Alias { aliasConstructor } = sentenceAliasAlias
                sentenceAliasLeftPattern =
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = aliasConstructor
                                , symbolOrAliasParams =
                                    SortVariableSort <$> aliasParams
                                }
                        , applicationChildren = variables
                        }
            sentenceAliasRightPattern <-
                Reader.local (addVariables variables)
                    (patGen sentenceAliasResultSort)
            sentenceAliasAttributes <- attributesGen
            return SentenceAlias
                { sentenceAliasAlias
                , sentenceAliasSorts
                , sentenceAliasResultSort
                , sentenceAliasLeftPattern
                , sentenceAliasRightPattern
                , sentenceAliasAttributes
                }

sentenceSymbolGen
    :: MetaOrObject level
    => Gen (SentenceSymbol level patternType)
sentenceSymbolGen = do
    sentenceSymbolSymbol <- symbolGen
    let Symbol { symbolParams } = sentenceSymbolSymbol
    Reader.local (addSortVariables symbolParams) $ do
        sentenceSymbolSorts <- couple sortGen
        sentenceSymbolResultSort <- sortGen
        sentenceSymbolAttributes <- attributesGen
        return SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }

sentenceImportGen :: Gen (SentenceImport patternType)
sentenceImportGen =
    SentenceImport
        <$> moduleNameGen
        <*> attributesGen

sentenceAxiomGen
   :: MetaOrObject level
   => Gen patternType
   -> Gen (SentenceAxiom (SortVariable level) patternType)
sentenceAxiomGen patGen = do
    sentenceAxiomParameters <- couple sortVariableGen
    Reader.local (addSortVariables sentenceAxiomParameters) $ do
        sentenceAxiomPattern <- patGen
        sentenceAxiomAttributes <- attributesGen
        return SentenceAxiom
            { sentenceAxiomParameters
            , sentenceAxiomPattern
            , sentenceAxiomAttributes
            }

unifiedSentenceAxiomGen
   :: Gen patternType
   -> Gen (SentenceAxiom (Unified SortVariable) patternType)
unifiedSentenceAxiomGen patGen = do
    sentenceAxiomParameters <- couple unifiedSortVariableGen
    Reader.local (addUnifiedSortVariables sentenceAxiomParameters) $ do
        sentenceAxiomPattern <- patGen
        sentenceAxiomAttributes <- attributesGen
        return SentenceAxiom
            { sentenceAxiomParameters
            , sentenceAxiomPattern
            , sentenceAxiomAttributes
            }

sentenceSortGen
    ::  forall level patternType.
        MetaOrObject level
    => Gen (SentenceSort level patternType)
sentenceSortGen = do
    sentenceSortName <- idGen (isMetaOrObject Proxy)
    sentenceSortParameters <- couple sortVariableGen
    sentenceSortAttributes <- attributesGen
    return SentenceSort
        { sentenceSortName
        , sentenceSortParameters
        , sentenceSortAttributes
        }

attributesGen :: Gen Attributes
attributesGen =
    Attributes <$> couple (korePatternChildGen =<< sortGen @Object)

koreSentenceGen :: Gen KoreSentence
koreSentenceGen =
    Gen.choice
        [ constructUnifiedSentence SentenceAliasSentence
            <$> sentenceAliasGen @Meta korePatternChildGen
        , constructUnifiedSentence SentenceSymbolSentence
            <$> sentenceSymbolGen @Meta
        , constructUnifiedSentence SentenceAliasSentence
            <$> sentenceAliasGen @Object korePatternChildGen
        , constructUnifiedSentence SentenceSymbolSentence
            <$> sentenceSymbolGen @Object
        , constructUnifiedSentence SentenceImportSentence
            <$> sentenceImportGen
        , asKoreAxiomSentence
            <$> unifiedSentenceAxiomGen korePatternUnifiedGen
        , asKoreClaimSentence
            <$> unifiedSentenceAxiomGen korePatternUnifiedGen
        , constructUnifiedSentence SentenceSortSentence
            <$> sentenceSortGen @Object
        , constructUnifiedSentence (SentenceHookSentence . SentenceHookedSort)
            <$> sentenceSortGen @Object
        , constructUnifiedSentence (SentenceHookSentence . SentenceHookedSymbol)
            <$> sentenceSymbolGen @Object
        ]

moduleGen
    :: Gen sentence
    -> Gen (Module sentence)
moduleGen senGen =
    Module
        <$> moduleNameGen
        <*> couple senGen
        <*> attributesGen

definitionGen
    :: Gen sentence
    -> Gen (Definition sentence)
definitionGen senGen =
    Definition
        <$> attributesGen
        <*> couple1 (moduleGen senGen)

metaMLPatternGen
    :: Sort Meta
    -> Gen (MetaMLPattern Variable (Valid (Variable Meta) Meta))
metaMLPatternGen patternSort =
    Gen.sized metaMLPatternGenWorker
  where
    metaMLPatternGenWorker n
      | n <= 1 =
        case () of
            () | patternSort == stringMetaSort ->
                 mkStringLiteral . getStringLiteral <$> stringLiteralGen
               | patternSort == charMetaSort ->
                 mkCharLiteral . getCharLiteral <$> charLiteralGen
               | otherwise ->
                 mkVar <$> variableGen patternSort
      | otherwise =
        (Gen.small . Gen.frequency)
            [ (1, metaMLPatternAndGen)
            , (1, metaMLPatternAppGen)
            , (1, metaMLPatternBottomGen)
            , (1, metaMLPatternCeilGen)
            , (1, metaMLPatternEqualsGen)
            , (1, metaMLPatternExistsGen)
            , (1, metaMLPatternFloorGen)
            , (1, metaMLPatternForallGen)
            , (1, metaMLPatternIffGen)
            , (1, metaMLPatternImpliesGen)
            , (1, metaMLPatternInGen)
            , (1, metaMLPatternNotGen)
            , (1, metaMLPatternOrGen)
            , (1, metaMLPatternTopGen)
            , (5, metaMLPatternVariableGen)
            ]
    metaMLPatternAndGen =
        mkAnd
            <$> metaMLPatternGen patternSort
            <*> metaMLPatternGen patternSort
    metaMLPatternAppGen =
        mkApp patternSort
            <$> symbolOrAliasGen
            <*> couple (metaMLPatternGen =<< sortGen)
    metaMLPatternBottomGen = pure (mkBottom patternSort)
    metaMLPatternCeilGen = do
        child <- metaMLPatternGen =<< sortGen
        pure (mkCeil patternSort child)
    metaMLPatternEqualsGen = do
        operandSort <- sortGen
        mkEquals patternSort
            <$> metaMLPatternGen operandSort
            <*> metaMLPatternGen operandSort
    metaMLPatternExistsGen = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (metaMLPatternGen patternSort)
        pure (mkExists var child)
    metaMLPatternForallGen = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (metaMLPatternGen patternSort)
        pure (mkForall var child)
    metaMLPatternFloorGen = do
        child <- metaMLPatternGen =<< sortGen
        pure (mkFloor patternSort child)
    metaMLPatternIffGen =
        mkIff
            <$> metaMLPatternGen patternSort
            <*> metaMLPatternGen patternSort
    metaMLPatternImpliesGen =
        mkImplies
            <$> metaMLPatternGen patternSort
            <*> metaMLPatternGen patternSort
    metaMLPatternInGen =
        mkIn patternSort
            <$> metaMLPatternGen patternSort
            <*> metaMLPatternGen patternSort
    metaMLPatternNotGen =
        mkNot <$> metaMLPatternGen patternSort
    metaMLPatternOrGen =
        mkOr
            <$> metaMLPatternGen patternSort
            <*> metaMLPatternGen patternSort
    metaMLPatternTopGen = pure (mkTop patternSort)
    metaMLPatternVariableGen = mkVar <$> variableGen patternSort

metaSentenceGen :: Gen MetaSentence
metaSentenceGen =
    eraseSentenceAnnotations <$> Gen.choice
        [ (SentenceSymbolSentence <$> sentenceSymbolGen)
        , (SentenceAliasSentence <$> sentenceAliasGen metaMLPatternGen)
        , (SentenceImportSentence <$> sentenceImportGen)
        , (SentenceAxiomSentence
            <$> sentenceAxiomGen (metaMLPatternGen =<< sortGen))
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

expandedPatternGen :: MetaOrObject level => Gen (CommonExpandedPattern level)
expandedPatternGen = do
    term <- stepPatternChildGen =<< sortGen
    return Predicated
        { term
        , predicate = makeTruePredicate
        , substitution = mempty
        }

orOfExpandedPatternGen
    :: MetaOrObject level
    => Gen (CommonOrOfExpandedPattern level)
orOfExpandedPatternGen =
    filterOr . MultiOr <$> Gen.list (Range.linear 0 64) expandedPatternGen
