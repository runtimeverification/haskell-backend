module Test.Kore (
    testId,
    Gen,
    standaloneGen,
    idGen,
    stringLiteralGen,
    symbolGen,
    aliasGen,
    sortVariableGen,
    sortGen,
    korePatternGen,
    attributesGen,
    koreSentenceGen,
    moduleGen,
    definitionGen,
    sortActual,
    sortVariable,
    sortVariableSort,
    predicateGen,
    predicateChildGen,
    elementVariableGen,
    configElementVariableGen,
    setVariableGen,
    elementTargetVariableGen,
    setTargetVariableGen,
    unifiedTargetVariableGen,
    unifiedVariableGen,
    genInternalInt,
    genInternalBool,
    genInternalString,
    couple,
    symbolOrAliasGen,
    addVariable,
    sentenceAxiomGen,
    korePatternUnifiedGen,
    TestLog (..),
    runTestLog,

    -- * Re-exports
    ParsedPattern,
    embedParsedPattern,
    Log.emptyLogger,
) where

import Control.Monad.Catch
import Control.Monad.Morph (MFunctor (..))
import Control.Monad.Reader (
    ReaderT,
 )
import qualified Control.Monad.Reader as Reader
import Control.Monad.State.Strict (
    StateT (..),
 )
import qualified Control.Monad.State.Strict as State
import qualified Data.Bifunctor as Bifunctor
import Data.Functor.Const
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import Hedgehog (
    MonadGen,
 )
import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (ApplicationSorts),
 )
import qualified Kore.Internal.ApplicationSorts as ApplicationSorts.DoNotUse
import Kore.Internal.InternalBool
import Kore.Internal.InternalInt
import Kore.Internal.InternalString
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Symbol as Internal (
    Symbol (Symbol),
 )
import Kore.Internal.TermLike as TermLike hiding (
    Alias,
    Symbol,
 )
import qualified Kore.Log as Log (
    Entry (toEntry),
    MonadLog (..),
    emptyLogger,
    toEntry,
 )
import Kore.Parser (
    embedParsedPattern,
 )
import Kore.Parser.Parser (
    parseVariableCounter,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkElementConfigVariable,
 )
import qualified Kore.Simplify.Simplify as SMT
import Kore.Syntax.Definition
import qualified Kore.Syntax.PatternF as Syntax
import Kore.Variables.Target (
    Target,
    mkElementNonTarget,
    mkElementTarget,
    mkSetNonTarget,
    mkSetTarget,
 )
import Log (SomeEntry)
import Prelude.Kore
import Prof (MonadProf)

-- | @Context@ stores the variables and sort variables in scope.
data Context = Context
    { objectVariables :: ![SomeVariable VariableName]
    , objectSortVariables :: ![SortVariable]
    , symbols :: !(Maybe [Internal.Symbol])
    , sorts :: !(Maybe [Sort])
    }

emptyContext :: Context
emptyContext =
    Context
        { objectVariables = []
        , objectSortVariables = []
        , symbols = Nothing
        , sorts = Nothing
        }

standaloneGen :: Gen a -> Hedgehog.Gen a
standaloneGen generator =
    Reader.runReaderT generator emptyContext

addVariable :: SomeVariable VariableName -> Context -> Context
addVariable var ctx@Context{objectVariables} =
    ctx{objectVariables = var : objectVariables}

addVariables :: [SomeVariable VariableName] -> Context -> Context
addVariables vars = \ctx -> foldr addVariable ctx vars

addSortVariable :: SortVariable -> Context -> Context
addSortVariable var ctx@Context{objectSortVariables} =
    ctx{objectSortVariables = var : objectSortVariables}

addSortVariables :: [SortVariable] -> Context -> Context
addSortVariables vars = \ctx -> foldr addSortVariable ctx vars

type Gen = ReaderT Context Hedgehog.Gen

couple :: MonadGen m => m a -> m [a]
couple = Gen.list (Range.linear 0 3)

couple1 :: MonadGen m => m a -> m [a]
couple1 = Gen.list (Range.linear 1 3)

genericIdGen :: MonadGen m => m Char -> m Char -> m Text
genericIdGen firstChar nextChar = do
    chars <-
        (:)
            <$> firstChar
            <*> Gen.list (Range.linear 0 32) nextChar
    return (Text.pack chars)

idGen :: MonadGen m => m Id
idGen = testId <$> objectIdGen

objectIdGen :: MonadGen m => m Text
objectIdGen =
    genericIdGen
        (Gen.element idFirstChars)
        (Gen.element $ idFirstChars ++ idOtherChars)
  where
    idFirstChars = ['A' .. 'Z'] <> ['a' .. 'z']
    idOtherChars = ['0' .. '9'] <> ['\'', '-']

setVarIdGen :: MonadGen m => m Id
setVarIdGen = testId <$> fmap ("@" <>) objectIdGen

stringLiteralGen :: MonadGen m => m StringLiteral
stringLiteralGen = StringLiteral <$> Gen.text (Range.linear 0 256) charGen

charGen :: MonadGen m => m Char
charGen =
    Gen.choice
        [ Gen.ascii
        , Gen.enum '\x80' '\xFF'
        , Gen.enum '\x100' '\xD7FF'
        , Gen.enum '\xE000' '\x10FFFF'
        ]

symbolOrAliasDeclarationRawGen ::
    MonadGen m =>
    (Id -> [SortVariable] -> result) ->
    m result
symbolOrAliasDeclarationRawGen constructor =
    constructor
        <$> Gen.small idGen
        <*> couple (Gen.small sortVariableGen)

symbolOrAliasGen :: Gen SymbolOrAlias
symbolOrAliasGen =
    SymbolOrAlias
        <$> Gen.small idGen
        <*> couple (Gen.small sortGen)

symbolGen :: MonadGen m => m Symbol
symbolGen = symbolOrAliasDeclarationRawGen Symbol

aliasGen :: MonadGen m => m Alias
aliasGen = symbolOrAliasDeclarationRawGen Alias

sortVariableGen :: MonadGen m => m SortVariable
sortVariableGen = SortVariable <$> idGen

sortActualGen :: Gen SortActual
sortActualGen =
    SortActual
        <$> Gen.small idGen
        <*> couple (Gen.small sortGen)

sortGen :: Gen Sort
sortGen = do
    Context{sorts} <- Reader.ask
    maybe randomSort Gen.element sorts
  where
    randomSort :: Gen Sort
    randomSort = do
        Context{objectSortVariables} <- Reader.ask
        sortGenWorker objectSortVariables

    sortGenWorker :: [SortVariable] -> Gen Sort
    sortGenWorker =
        \case
            [] -> actualSort
            sortVariables ->
                Gen.choice
                    [ SortVariableSort <$> Gen.element sortVariables
                    , actualSort
                    ]
      where
        actualSort = SortActualSort <$> sortActualGen

moduleNameGen :: MonadGen m => m ModuleName
moduleNameGen = ModuleName <$> objectIdGen

variableGen' ::
    Sort ->
    [Variable VariableName] ->
    Gen Id ->
    Gen (Variable VariableName)
variableGen' patternSort variables genId =
    case filter bySort variables of
        [] -> freshVariable
        variables' ->
            Gen.choice
                [ Gen.element variables'
                , freshVariable
                ]
  where
    bySort Variable{variableSort} = variableSort == patternSort
    freshVariable = do
        (base, counter) <- parseVariableCounter <$> genId
        let variableName = VariableName{base, counter}
        pure Variable{variableName, variableSort = patternSort}

elementVariableGen :: Sort -> Gen (ElementVariable VariableName)
elementVariableGen patternSort = do
    Context{objectVariables} <- Reader.ask
    let elementVariables = mapMaybe retractElementVariable objectVariables
        variables = (fmap . fmap) unElementVariableName elementVariables
    variableGen' patternSort variables idGen
        & (fmap . fmap) ElementVariableName

configElementVariableGen :: Sort -> Gen (ElementVariable RewritingVariableName)
configElementVariableGen patternSort =
    elementVariableGen patternSort <&> mkElementConfigVariable

setVariableGen :: Sort -> Gen (SetVariable VariableName)
setVariableGen sort = do
    Context{objectVariables} <- Reader.ask
    let setVariables = mapMaybe retractSetVariable objectVariables
        variables = (fmap . fmap) unSetVariableName setVariables
    variableGen' sort variables setVarIdGen
        & (fmap . fmap) SetVariableName

unifiedVariableGen :: Sort -> Gen (SomeVariable VariableName)
unifiedVariableGen sort =
    Gen.choice
        [ fmap inject <$> elementVariableGen sort
        , fmap inject <$> setVariableGen sort
        ]

elementTargetVariableGen :: Sort -> Gen (ElementVariable (Target VariableName))
elementTargetVariableGen sort =
    Gen.choice
        [ mkElementTarget <$> elementVariableGen sort
        , mkElementNonTarget <$> elementVariableGen sort
        ]

setTargetVariableGen :: Sort -> Gen (SetVariable (Target VariableName))
setTargetVariableGen sort =
    Gen.choice
        [ mkSetTarget <$> setVariableGen sort
        , mkSetNonTarget <$> setVariableGen sort
        ]

unifiedTargetVariableGen :: Sort -> Gen (SomeVariable (Target VariableName))
unifiedTargetVariableGen sort =
    Gen.choice
        [ fmap inject <$> elementTargetVariableGen sort
        , fmap inject <$> setTargetVariableGen sort
        ]

unaryOperatorGen ::
    MonadGen m =>
    (Sort -> child -> result) ->
    (Sort -> m child) ->
    Sort ->
    m result
unaryOperatorGen constructor childGen patternSort =
    constructor patternSort <$> Gen.small (childGen patternSort)

binaryOperatorGen ::
    (Sort -> child -> child -> b child) ->
    (Sort -> Gen child) ->
    Sort ->
    Gen (b child)
binaryOperatorGen constructor childGen patternSort =
    constructor patternSort
        <$> Gen.small (childGen patternSort)
        <*> Gen.small (childGen patternSort)

ceilFloorGen ::
    (Sort -> Sort -> child -> c child) ->
    (Sort -> Gen child) ->
    Sort ->
    Gen (c child)
ceilFloorGen constructor childGen resultSort = do
    operandSort <- Gen.small sortGen
    constructor resultSort operandSort <$> Gen.small (childGen operandSort)

equalsInGen ::
    (Sort -> Sort -> child -> child -> c child) ->
    (Sort -> Gen child) ->
    Sort ->
    Gen (c child)
equalsInGen constructor childGen resultSort = do
    operandSort <- Gen.small sortGen
    constructor resultSort operandSort
        <$> Gen.small (childGen operandSort)
        <*> Gen.small (childGen operandSort)

existsForallGen ::
    (Sort -> ElementVariable VariableName -> child -> q child) ->
    (Sort -> Gen child) ->
    Sort ->
    Gen (q child)
existsForallGen constructor childGen patternSort = do
    varSort <- Gen.small sortGen
    var <- Gen.small (elementVariableGen varSort)
    child <-
        Gen.small
            (Reader.local (addVariable (inject var)) $ childGen patternSort)
    return (constructor patternSort var child)

topBottomGen :: (Sort -> t child) -> Sort -> Gen (t child)
topBottomGen constructor = pure . constructor

andGen :: (Sort -> Gen child) -> Sort -> Gen (And Sort child)
andGen = binaryOperatorGen And

applicationGen ::
    (Sort -> Gen child) ->
    Sort ->
    Gen (Application SymbolOrAlias child)
applicationGen childGen sort = do
    Context{symbols} <- Reader.ask
    case symbols of
        Nothing -> randomApplication
        Just allowedSymbols ->
            applicationFromList (filter (hasResultSort sort) allowedSymbols)
  where
    randomApplication =
        Application
            <$> Gen.small symbolOrAliasGen
            <*> couple (Gen.small (childGen =<< sortGen))

    applicationFromList [] = randomApplication
    applicationFromList symbols = do
        Internal.Symbol
            { symbolConstructor
            , symbolParams
            , symbolSorts = ApplicationSorts{applicationSortsOperands}
            } <-
            Gen.element symbols
        case symbolParams of
            [] -> do
                children <- mapM childGen applicationSortsOperands
                return
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor = symbolConstructor
                                , symbolOrAliasParams = []
                                }
                        , applicationChildren = children
                        }
            _ -> randomApplication

    hasResultSort
        expectedSort
        Internal.Symbol
            { symbolSorts = ApplicationSorts{applicationSortsResult}
            } =
            expectedSort == applicationSortsResult

bottomGen :: Sort -> Gen (Bottom Sort child)
bottomGen = topBottomGen Bottom

ceilGen :: (Sort -> Gen child) -> Sort -> Gen (Ceil Sort child)
ceilGen = ceilFloorGen Ceil

equalsGen :: (Sort -> Gen child) -> Sort -> Gen (Equals Sort child)
equalsGen = equalsInGen Equals

genDomainValue :: (Sort -> Gen child) -> Sort -> Gen (DomainValue Sort child)
genDomainValue childGen domainValueSort =
    DomainValue domainValueSort <$> childGen stringMetaSort

genInternalInt :: Sort -> Gen InternalInt
genInternalInt builtinIntSort =
    InternalInt builtinIntSort <$> genInteger
  where
    genInteger = Gen.integral (Range.linear (-1024) 1024)

genInternalBool :: Sort -> Gen InternalBool
genInternalBool builtinBoolSort =
    InternalBool builtinBoolSort <$> Gen.bool

genInternalString :: Sort -> Gen InternalString
genInternalString internalStringSort =
    InternalString internalStringSort
        <$> Gen.text (Range.linear 0 1024) (Reader.lift Gen.unicode)

existsGen :: (Sort -> Gen child) -> Sort -> Gen (Exists Sort VariableName child)
existsGen = existsForallGen Exists

floorGen :: (Sort -> Gen child) -> Sort -> Gen (Floor Sort child)
floorGen = ceilFloorGen Floor

forallGen :: (Sort -> Gen child) -> Sort -> Gen (Forall Sort VariableName child)
forallGen = existsForallGen Forall

iffGen :: (Sort -> Gen child) -> Sort -> Gen (Iff Sort child)
iffGen = binaryOperatorGen Iff

impliesGen :: (Sort -> Gen child) -> Sort -> Gen (Implies Sort child)
impliesGen = binaryOperatorGen Implies

inGen :: (Sort -> Gen child) -> Sort -> Gen (In Sort child)
inGen = equalsInGen In

nextGen :: (Sort -> Gen child) -> Sort -> Gen (Next Sort child)
nextGen = unaryOperatorGen Next

notGen :: (Sort -> Gen child) -> Sort -> Gen (Not Sort child)
notGen = unaryOperatorGen Not

orGen :: (Sort -> Gen child) -> Sort -> Gen (Or Sort child)
orGen = binaryOperatorGen Or

rewritesGen :: (Sort -> Gen child) -> Sort -> Gen (Rewrites Sort child)
rewritesGen = binaryOperatorGen Rewrites

topGen :: Sort -> Gen (Top Sort child)
topGen = topBottomGen Top

patternGen ::
    (Sort -> Gen child) ->
    Sort ->
    Gen (Syntax.PatternF VariableName child)
patternGen childGen patternSort =
    Gen.frequency
        [ (1, Syntax.AndF <$> andGen childGen patternSort)
        , (1, Syntax.ApplicationF <$> applicationGen childGen patternSort)
        , (1, Syntax.BottomF <$> bottomGen patternSort)
        , (1, Syntax.CeilF <$> ceilGen childGen patternSort)
        , (1, Syntax.EqualsF <$> equalsGen childGen patternSort)
        , (1, Syntax.ExistsF <$> existsGen childGen patternSort)
        , (1, Syntax.FloorF <$> floorGen childGen patternSort)
        , (1, Syntax.ForallF <$> forallGen childGen patternSort)
        , (1, Syntax.IffF <$> iffGen childGen patternSort)
        , (1, Syntax.ImpliesF <$> impliesGen childGen patternSort)
        , (1, Syntax.InF <$> inGen childGen patternSort)
        , (1, Syntax.NotF <$> notGen childGen patternSort)
        , (1, Syntax.OrF <$> orGen childGen patternSort)
        , (1, Syntax.TopF <$> topGen patternSort)
        , (5, Syntax.VariableF . Const <$> unifiedVariableGen patternSort)
        ]

korePatternGen :: Hedgehog.Gen ParsedPattern
korePatternGen =
    standaloneGen (korePatternChildGen =<< sortGen)

korePatternChildGen :: Sort -> Gen ParsedPattern
korePatternChildGen patternSort' =
    Gen.sized korePatternChildGenWorker
  where
    korePatternChildGenWorker n
        | n <= 1 =
            case () of
                ()
                    | patternSort' == stringMetaSort ->
                        korePatternGenStringLiteral
                    | otherwise ->
                        Gen.choice [korePatternGenVariable, korePatternGenDomainValue]
        | otherwise =
            case () of
                () ->
                    Gen.frequency
                        [ (15, korePatternGenLevel)
                        , (1, korePatternGenNext)
                        , (1, korePatternGenRewrites)
                        ]

    korePatternGenLevel :: Gen ParsedPattern
    korePatternGenLevel =
        embedParsedPattern <$> patternGen korePatternChildGen patternSort'

    korePatternGenStringLiteral :: Gen ParsedPattern
    korePatternGenStringLiteral =
        embedParsedPattern . Syntax.StringLiteralF . Const
            <$> stringLiteralGen

    korePatternGenDomainValue :: Gen ParsedPattern
    korePatternGenDomainValue =
        embedParsedPattern . Syntax.DomainValueF
            <$> genDomainValue korePatternChildGen patternSort'

    korePatternGenNext :: Gen ParsedPattern
    korePatternGenNext =
        embedParsedPattern . Syntax.NextF
            <$> nextGen korePatternChildGen patternSort'

    korePatternGenRewrites :: Gen ParsedPattern
    korePatternGenRewrites =
        embedParsedPattern . Syntax.RewritesF
            <$> rewritesGen korePatternChildGen patternSort'

    korePatternGenVariable :: Gen ParsedPattern
    korePatternGenVariable =
        embedParsedPattern . Syntax.VariableF . Const
            <$> unifiedVariableGen patternSort'

korePatternUnifiedGen :: Gen ParsedPattern
korePatternUnifiedGen = korePatternChildGen =<< sortGen

predicateGen ::
    Gen (TermLike VariableName) ->
    Hedgehog.Gen (Predicate VariableName)
predicateGen childGen =
    standaloneGen (predicateChildGen childGen Nothing =<< sortGen)

predicateChildGen ::
    Gen (TermLike VariableName) ->
    Maybe Sort ->
    Sort ->
    Gen (Predicate VariableName)
predicateChildGen childGen quantifierSort patternSort' =
    Gen.recursive
        Gen.choice
        -- non-recursive generators
        [ pure Predicate.makeFalsePredicate
        , pure Predicate.makeTruePredicate
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
    go = predicateChildGen childGen quantifierSort
    quantifierSortGen = case quantifierSort of
        Nothing -> sortGen
        Just qSort -> pure qSort
    predicateChildGenAnd =
        Predicate.makeAndPredicate
            <$> go patternSort'
            <*> go patternSort'
    predicateChildGenOr =
        Predicate.makeOrPredicate
            <$> go patternSort'
            <*> go patternSort'
    predicateChildGenIff =
        Predicate.makeIffPredicate
            <$> go patternSort'
            <*> go patternSort'
    predicateChildGenImplies =
        Predicate.makeImpliesPredicate
            <$> go patternSort'
            <*> go patternSort'
    predicateChildGenCeil = Predicate.makeCeilPredicate <$> childGen
    predicateChildGenFloor = Predicate.makeFloorPredicate <$> childGen
    predicateChildGenEquals =
        Predicate.makeEqualsPredicate <$> childGen <*> childGen
    predicateChildGenIn =
        Predicate.makeInPredicate <$> childGen <*> childGen
    predicateChildGenNot =
        Predicate.makeNotPredicate
            <$> go patternSort'
    predicateChildGenExists = do
        varSort <- quantifierSortGen
        var <- elementVariableGen varSort
        child <-
            Reader.local
                (addVariable (inject var))
                (go patternSort')
        return (Predicate.makeExistsPredicate var child)
    predicateChildGenForall = do
        varSort <- quantifierSortGen
        var <- elementVariableGen varSort
        child <-
            Reader.local
                (addVariable (inject var))
                (go patternSort')
        return (Predicate.makeForallPredicate var child)

sentenceAliasGen ::
    (Sort -> Gen patternType) ->
    Gen (SentenceAlias patternType)
sentenceAliasGen patGen =
    Gen.small sentenceAliasGenWorker
  where
    sentenceAliasGenWorker = do
        sentenceAliasAlias <- aliasGen
        let Alias{aliasParams} = sentenceAliasAlias
        Reader.local (addSortVariables aliasParams) $ do
            sentenceAliasSorts <- couple sortGen
            sentenceAliasResultSort <- sortGen
            variables <- traverse unifiedVariableGen sentenceAliasSorts
            let Alias{aliasConstructor} = sentenceAliasAlias
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
                Reader.local
                    (addVariables variables)
                    (patGen sentenceAliasResultSort)
            sentenceAliasAttributes <- attributesGen
            return
                SentenceAlias
                    { sentenceAliasAlias
                    , sentenceAliasSorts
                    , sentenceAliasResultSort
                    , sentenceAliasLeftPattern
                    , sentenceAliasRightPattern
                    , sentenceAliasAttributes
                    }

sentenceSymbolGen :: Gen SentenceSymbol
sentenceSymbolGen = do
    sentenceSymbolSymbol <- symbolGen
    let Symbol{symbolParams} = sentenceSymbolSymbol
    Reader.local (addSortVariables symbolParams) $ do
        sentenceSymbolSorts <- couple sortGen
        sentenceSymbolResultSort <- sortGen
        sentenceSymbolAttributes <- attributesGen
        return
            SentenceSymbol
                { sentenceSymbolSymbol
                , sentenceSymbolSorts
                , sentenceSymbolResultSort
                , sentenceSymbolAttributes
                }

sentenceImportGen :: Gen SentenceImport
sentenceImportGen =
    SentenceImport
        <$> moduleNameGen
        <*> attributesGen

sentenceAxiomGen ::
    Gen patternType ->
    Gen (SentenceAxiom patternType)
sentenceAxiomGen patGen = do
    sentenceAxiomParameters <- couple sortVariableGen
    Reader.local (addSortVariables sentenceAxiomParameters) $ do
        sentenceAxiomPattern <- patGen
        sentenceAxiomAttributes <- attributesGen
        return
            SentenceAxiom
                { sentenceAxiomParameters
                , sentenceAxiomPattern
                , sentenceAxiomAttributes
                }

sentenceSortGen :: Gen SentenceSort
sentenceSortGen = do
    sentenceSortName <- idGen
    sentenceSortParameters <- couple sortVariableGen
    sentenceSortAttributes <- attributesGen
    return
        SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            , sentenceSortAttributes
            }

attributesGen :: Gen Attributes
attributesGen = Attributes <$> couple (korePatternChildGen =<< sortGen)

koreSentenceGen :: Gen ParsedSentence
koreSentenceGen =
    Gen.choice
        [ SentenceAliasSentence <$> sentenceAliasGen korePatternChildGen
        , SentenceSymbolSentence <$> sentenceSymbolGen
        , SentenceImportSentence
            <$> sentenceImportGen
        , SentenceAxiomSentence <$> sentenceAxiomGen korePatternUnifiedGen
        , SentenceClaimSentence . SentenceClaim
            <$> sentenceAxiomGen korePatternUnifiedGen
        , SentenceSortSentence <$> sentenceSortGen
        , SentenceHookSentence . SentenceHookedSort <$> sentenceSortGen
        , SentenceHookSentence . SentenceHookedSymbol <$> sentenceSymbolGen
        ]

moduleGen ::
    Gen sentence ->
    Gen (Module sentence)
moduleGen senGen =
    Module
        <$> moduleNameGen
        <*> couple senGen
        <*> attributesGen

definitionGen ::
    Gen sentence ->
    Gen (Definition sentence)
definitionGen senGen =
    Definition
        <$> attributesGen
        <*> couple1 (moduleGen senGen)

testId :: Text -> Id
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }

sortVariable :: Text -> SortVariable
sortVariable name =
    SortVariable{getSortVariable = testId name}

sortVariableSort :: Text -> Sort
sortVariableSort name =
    SortVariableSort (sortVariable name)

sortActual :: Text -> [Sort] -> Sort
sortActual name sorts =
    SortActualSort
        SortActual
            { sortActualName = testId name
            , sortActualSorts = sorts
            }

newtype TestLog m a = TestLog {logState :: StateT [SomeEntry] m a}
    deriving newtype (Functor, Applicative, Monad)
    deriving newtype (State.MonadState [SomeEntry], MonadIO, SMT.MonadSMT)
    deriving newtype (MonadThrow, MonadCatch, MonadMask, MonadProf)

instance Monad m => Log.MonadLog (TestLog m) where
    logEntry entry = State.modify (Log.toEntry entry :)
    logWhile entry (TestLog state) =
        TestLog $ State.mapStateT addEntry state
      where
        addEntry :: m (a, [SomeEntry]) -> m (a, [SomeEntry])
        addEntry = fmap $ Bifunctor.second (Log.toEntry entry :)

instance MonadTrans TestLog where
    lift ma = TestLog $ StateT $ \s -> fmap (flip (,) s) ma

instance MFunctor TestLog where
    hoist f (TestLog (StateT state)) =
        TestLog $
            StateT $
                \s -> f (state s)

instance SMT.MonadSimplify m => SMT.MonadSimplify (TestLog m)

runTestLog ::
    (m (a, [SomeEntry]) -> IO (a, [SomeEntry])) ->
    TestLog m a ->
    IO (a, [SomeEntry])
runTestLog run (TestLog state) = run $ State.runStateT state []
