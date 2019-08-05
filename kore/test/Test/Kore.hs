module Test.Kore
    ( testId
    , Gen
    , standaloneGen
    , idGen
    , stringLiteralGen
    , charLiteralGen
    , symbolGen
    , aliasGen
    , sortVariableGen
    , sortGen
    , korePatternGen
    , attributesGen
    , koreSentenceGen
    , moduleGen
    , definitionGen
    , sortActual
    , sortVariable
    , sortVariableSort
    , predicateGen
    , predicateChildGen
    , variableGen
    , genBuiltin
    , couple
    , symbolOrAliasGen
    , addVariable
      -- * Re-exports
    , ParsedPattern
    , asParsedPattern
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
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import qualified Kore.Domain.Builtin as Domain
import           Kore.Internal.TermLike as TermLike hiding
                 ( Alias, Symbol )
import qualified Kore.Logger.Output as Logger
                 ( emptyLogger )
import           Kore.Parser
                 ( ParsedPattern, asParsedPattern )
import           Kore.Parser.Lexeme
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Syntax.Definition
import qualified Kore.Syntax.PatternF as Syntax
                 ( PatternF (..) )

{- | @Context@ stores the variables and sort variables in scope.
 -}
data Context =
    Context
        { objectVariables :: ![Variable]
        , objectSortVariables :: ![SortVariable]
        }

emptyContext :: Context
emptyContext =
    Context
        { objectVariables = []
        , objectSortVariables = []
        }

standaloneGen :: Gen a -> Hedgehog.Gen a
standaloneGen generator =
    Reader.runReaderT generator emptyContext

addVariable :: Variable -> Context -> Context
addVariable var ctx@Context { objectVariables } =
    ctx { objectVariables = var : objectVariables }

addVariables :: [Variable] -> Context -> Context
addVariables vars = \ctx -> foldr addVariable ctx vars

addSortVariable :: SortVariable -> Context -> Context
addSortVariable var ctx@Context { objectSortVariables } =
    ctx { objectSortVariables = var : objectSortVariables }

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

stringLiteralGen :: MonadGen m => m (StringLiteral child)
stringLiteralGen =
    StringLiteral <$> Gen.text (Range.linear 0 256) charGen

charLiteralGen :: MonadGen m => m (CharLiteral child)
charLiteralGen = CharLiteral <$> charGen

charGen :: MonadGen m => m Char
charGen =
    Gen.choice
        [ Gen.ascii
        , Gen.enum '\x80' '\xFF'
        , Gen.enum '\x100' '\xD7FF'
        , Gen.enum '\xE000' '\x10FFFF'
        ]

symbolOrAliasDeclarationRawGen
    :: MonadGen m
    => (Id -> [SortVariable] -> result)
    -> m result
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
    Context { objectSortVariables } <- Reader.ask
    sortGenWorker objectSortVariables
  where
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

variableGen :: Sort -> Gen Variable
variableGen patternSort = do
    Context { objectVariables } <- Reader.ask
    variableGenWorker objectVariables
  where
    bySort Variable { variableSort } = variableSort == patternSort
    variableGenWorker :: [Variable] -> Gen Variable
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
            Variable <$> idGen <*> pure mempty <*> pure patternSort

unaryOperatorGen
    :: MonadGen m
    => (Sort -> child -> result)
    -> (Sort -> m child)
    -> Sort
    -> m result
unaryOperatorGen constructor childGen patternSort =
    constructor patternSort <$> Gen.small (childGen patternSort)

binaryOperatorGen
    :: (Sort -> child -> child -> b child)
    -> (Sort -> Gen child)
    -> Sort
    -> Gen (b child)
binaryOperatorGen constructor childGen patternSort =
    constructor patternSort
        <$> Gen.small (childGen patternSort)
        <*> Gen.small (childGen patternSort)

ceilFloorGen
    :: (Sort -> Sort -> child -> c child)
    -> (Sort -> Gen child)
    -> Sort
    -> Gen (c child)
ceilFloorGen constructor childGen resultSort = do
    operandSort <- Gen.small sortGen
    constructor resultSort operandSort <$> Gen.small (childGen operandSort)

equalsInGen
    :: (Sort -> Sort -> child -> child -> c child)
    -> (Sort -> Gen child)
    -> Sort
    -> Gen (c child)
equalsInGen constructor childGen resultSort = do
    operandSort <- Gen.small sortGen
    constructor resultSort operandSort
        <$> Gen.small (childGen operandSort)
        <*> Gen.small (childGen operandSort)

existsForallGen
    :: (Sort -> Variable -> child -> q child)
    -> (Sort -> Gen child)
    -> Sort
    -> Gen (q child)
existsForallGen constructor childGen patternSort = do
    varSort <- Gen.small sortGen
    var <- Gen.small (variableGen varSort)
    constructor patternSort var
        <$> Gen.small (Reader.local (addVariable var) $ childGen patternSort)

topBottomGen :: (Sort -> t child) -> Sort -> Gen (t child)
topBottomGen constructor = pure . constructor

andGen :: (Sort -> Gen child) -> Sort -> Gen (And Sort child)
andGen = binaryOperatorGen And

applicationGen
    :: (Sort -> Gen child)
    -> Sort
    -> Gen (Application SymbolOrAlias child)
applicationGen childGen _ =
    Application
        <$> Gen.small symbolOrAliasGen
        <*> couple (Gen.small (childGen =<< sortGen))

bottomGen :: Sort -> Gen (Bottom Sort child)
bottomGen = topBottomGen Bottom

ceilGen :: (Sort -> Gen child) -> Sort -> Gen (Ceil Sort child)
ceilGen = ceilFloorGen Ceil

equalsGen :: (Sort -> Gen child) -> Sort -> Gen (Equals Sort child)
equalsGen = equalsInGen Equals

genDomainValue :: (Sort -> Gen child) -> Sort -> Gen (DomainValue Sort child)
genDomainValue childGen domainValueSort =
    DomainValue domainValueSort <$> childGen stringMetaSort

genBuiltin :: Sort -> Gen (TermLike.Builtin (TermLike variable))
genBuiltin domainValueSort = Gen.choice
    [ Domain.BuiltinInt <$> genInternalInt domainValueSort
    , Domain.BuiltinBool <$> genInternalBool domainValueSort
    , Domain.BuiltinString <$> genInternalString domainValueSort
    ]

genInternalInt :: Sort -> Gen Domain.InternalInt
genInternalInt builtinIntSort =
    Domain.InternalInt builtinIntSort <$> genInteger
  where
    genInteger = Gen.integral (Range.linear (-1024) 1024)

genInternalBool :: Sort -> Gen Domain.InternalBool
genInternalBool builtinBoolSort =
    Domain.InternalBool builtinBoolSort <$> Gen.bool

genInternalString :: Sort -> Gen Domain.InternalString
genInternalString internalStringSort =
    Domain.InternalString internalStringSort
    <$> Gen.text (Range.linear 0 1024) Gen.unicode

existsGen :: (Sort -> Gen child) -> Sort -> Gen (Exists Sort Variable child)
existsGen = existsForallGen Exists

floorGen :: (Sort -> Gen child) -> Sort -> Gen (Floor Sort child)
floorGen = ceilFloorGen Floor

forallGen :: (Sort -> Gen child) -> Sort -> Gen (Forall Sort Variable child)
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

patternGen
    :: (Sort -> Gen child)
    -> Sort
    -> Gen (Syntax.PatternF Variable child)
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
        , (5, Syntax.VariableF <$> variableGen patternSort)
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
              | patternSort' == charMetaSort ->
                korePatternGenCharLiteral
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
        asParsedPattern <$> patternGen korePatternChildGen patternSort'

    korePatternGenStringLiteral :: Gen ParsedPattern
    korePatternGenStringLiteral =
        asParsedPattern . Syntax.StringLiteralF <$> stringLiteralGen

    korePatternGenCharLiteral :: Gen ParsedPattern
    korePatternGenCharLiteral =
        asParsedPattern . Syntax.CharLiteralF <$> charLiteralGen

    korePatternGenDomainValue :: Gen ParsedPattern
    korePatternGenDomainValue =
        asParsedPattern . Syntax.DomainValueF
            <$> genDomainValue korePatternChildGen patternSort'

    korePatternGenNext :: Gen ParsedPattern
    korePatternGenNext =
        asParsedPattern . Syntax.NextF
            <$> nextGen korePatternChildGen patternSort'

    korePatternGenRewrites :: Gen ParsedPattern
    korePatternGenRewrites =
        asParsedPattern . Syntax.RewritesF
            <$> rewritesGen korePatternChildGen patternSort'

    korePatternGenVariable :: Gen ParsedPattern
    korePatternGenVariable =
        asParsedPattern . Syntax.VariableF <$> variableGen patternSort'

korePatternUnifiedGen :: Gen ParsedPattern
korePatternUnifiedGen = korePatternChildGen =<< sortGen

predicateGen
    :: Gen (TermLike Variable)
    -> Hedgehog.Gen (Syntax.Predicate Variable)
predicateGen childGen = standaloneGen (predicateChildGen childGen =<< sortGen)

predicateChildGen
    :: Gen (TermLike Variable)
    -> Sort
    -> Gen (Syntax.Predicate Variable)
predicateChildGen childGen patternSort' =
    Gen.recursive
        Gen.choice
        -- non-recursive generators
        [ pure Syntax.Predicate.makeFalsePredicate
        , pure Syntax.Predicate.makeTruePredicate
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
        Syntax.Predicate.makeAndPredicate
            <$> predicateChildGen childGen patternSort'
            <*> predicateChildGen childGen patternSort'
    predicateChildGenOr =
        Syntax.Predicate.makeOrPredicate
            <$> predicateChildGen childGen patternSort'
            <*> predicateChildGen childGen patternSort'
    predicateChildGenIff =
        Syntax.Predicate.makeIffPredicate
            <$> predicateChildGen childGen patternSort'
            <*> predicateChildGen childGen patternSort'
    predicateChildGenImplies =
        Syntax.Predicate.makeImpliesPredicate
            <$> predicateChildGen childGen patternSort'
            <*> predicateChildGen childGen patternSort'
    predicateChildGenCeil = Syntax.Predicate.makeCeilPredicate <$> childGen
    predicateChildGenFloor = Syntax.Predicate.makeFloorPredicate <$> childGen
    predicateChildGenEquals =
        Syntax.Predicate.makeEqualsPredicate <$> childGen <*> childGen
    predicateChildGenIn =
        Syntax.Predicate.makeInPredicate <$> childGen <*> childGen
    predicateChildGenNot =
        Syntax.Predicate.makeNotPredicate
            <$> predicateChildGen childGen patternSort'
    predicateChildGenExists = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (predicateChildGen childGen patternSort')
        return (Syntax.Predicate.makeExistsPredicate var child)
    predicateChildGenForall = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (predicateChildGen childGen patternSort')
        return (Syntax.Predicate.makeForallPredicate var child)

sentenceAliasGen
    :: (Sort -> Gen patternType)
    -> Gen (SentenceAlias patternType)
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

sentenceSymbolGen :: Gen (SentenceSymbol patternType)
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
   :: Gen patternType
   -> Gen (SentenceAxiom patternType)
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

sentenceSortGen
    :: forall patternType
    .  Gen (SentenceSort patternType)
sentenceSortGen = do
    sentenceSortName <- idGen
    sentenceSortParameters <- couple sortVariableGen
    sentenceSortAttributes <- attributesGen
    return SentenceSort
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

testId :: Text -> Id
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }

sortVariable :: Text -> SortVariable
sortVariable name =
    SortVariable { getSortVariable = testId name }

sortVariableSort :: Text -> Sort
sortVariableSort name =
    SortVariableSort (sortVariable name)

sortActual :: Text -> [Sort] -> Sort
sortActual name sorts =
    SortActualSort SortActual
        { sortActualName = testId name
        , sortActualSorts = sorts
        }
