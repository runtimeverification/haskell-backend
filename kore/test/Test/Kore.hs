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
    , korePatternGen
    , attributesGen
    , koreSentenceGen
    , moduleGen
    , definitionGen
    , sortActual
    , sortVariable
    , sortVariableSort
    , termLikeGen
    , expandedPatternGen
    , orPatternGen
    , predicateGen
    , predicateChildGen
    , variableGen
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
import           Data.Proxy
import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import qualified Kore.AST.Common as Common
import qualified Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Logger.Output as Logger
                 ( emptyLogger )
import           Kore.Parser
                 ( ParsedPattern, asParsedPattern )
import           Kore.Parser.Lexeme
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Sort
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern as Pattern
import           Kore.Step.TermLike as TermLike

{- | @Context@ stores the variables and sort variables in scope.
 -}
data Context =
    Context
        { objectVariables :: ![Variable Object]
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

addVariable
    :: MetaOrObject level
    => Variable level
    -> Context
    -> Context
addVariable var =
    case isMetaOrObject var of
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
    => SortVariable
    -> Context
    -> Context
addSortVariable var ctx@Context { objectSortVariables } =
    ctx { objectSortVariables = var : objectSortVariables }

addSortVariables
    ::  forall level.
        MetaOrObject level
    => [SortVariable]
    -> Context
    -> Context
addSortVariables vars = \ctx -> foldr addSortVariable ctx vars

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

idGen :: MonadGen m => IsMetaOrObject level -> m Id
idGen =
    \case
        IsObject -> testId <$> objectIdGen

objectIdGen :: MonadGen m => m Text
objectIdGen =
    genericIdGen
        (Gen.element idFirstChars)
        (Gen.element $ idFirstChars ++ idOtherChars)

stringLiteralGen :: MonadGen m => m StringLiteral
stringLiteralGen =
    Common.StringLiteral <$> Gen.text (Range.linear 0 256) charGen

charLiteralGen :: MonadGen m => m CharLiteral
charLiteralGen = Common.CharLiteral <$> charGen

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
    => (Id -> [Sort level] -> s level)
    -> Gen (s level)
symbolOrAliasRawGen constructor =
    constructor
        <$> Gen.small (idGen level)
        <*> couple (Gen.small sortGen)
  where
    level = isMetaOrObject Proxy

symbolOrAliasDeclarationRawGen
    :: (MetaOrObject level, MonadGen m)
    => (Id -> [SortVariable] -> s level)
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

sortVariableGen :: (MetaOrObject level, MonadGen m) => m SortVariable
sortVariableGen = SortVariable <$> idGen (isMetaOrObject Proxy)

sortActualGen :: IsMetaOrObject level -> Gen (SortActual level)
sortActualGen =
    \case
        IsObject ->
            SortActual
                <$> Gen.small (idGen IsObject)
                <*> couple (Gen.small sortGen)

sortGen :: forall level. MetaOrObject level => Gen (Sort level)
sortGen =
    case level of
        IsObject -> do
            Context { objectSortVariables } <- Reader.ask
            sortGenWorker objectSortVariables
  where
    level = isMetaOrObject (Proxy @level)
    sortGenWorker :: [SortVariable] -> Gen (Sort level)
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

moduleNameGen :: MonadGen m => m ModuleName
moduleNameGen = ModuleName <$> objectIdGen

variableGen
    ::  forall level.
        MetaOrObject level
    => Sort level
    -> Gen (Variable level)
variableGen patternSort =
    case level of
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
andGen = binaryOperatorGen Common.And

applicationGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Application level child)
applicationGen childGen _ =
    Common.Application
        <$> Gen.small symbolOrAliasGen
        <*> couple (Gen.small (childGen =<< sortGen))

bottomGen :: Sort level -> Gen (Bottom level child)
bottomGen = topBottomGen Common.Bottom

ceilGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Ceil level child)
ceilGen = ceilFloorGen Common.Ceil

equalsGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Equals level child)
equalsGen = equalsInGen Common.Equals

genBuiltinExternal :: Sort Object -> Gen (Domain.Builtin child)
genBuiltinExternal domainValueSort =
    Domain.BuiltinExternal <$> genExternal domainValueSort

genBuiltin :: Sort Object -> Gen (Domain.Builtin child)
genBuiltin domainValueSort = Gen.choice
    [ genBuiltinExternal domainValueSort
    , Domain.BuiltinInt <$> genInternalInt domainValueSort
    , Domain.BuiltinBool <$> genInternalBool domainValueSort
    ]

genInternalInt :: Sort Object -> Gen Domain.InternalInt
genInternalInt builtinIntSort =
    Domain.InternalInt builtinIntSort <$> genInteger
  where
    genInteger = Gen.integral (Range.linear (-1024) 1024)

genInternalBool :: Sort Object -> Gen Domain.InternalBool
genInternalBool builtinBoolSort =
    Domain.InternalBool builtinBoolSort <$> Gen.bool

genExternal :: Sort Object -> Gen (Domain.External child)
genExternal domainValueSort =
    Domain.External
        domainValueSort
        . Kore.AST.Pure.eraseAnnotations
        . mkStringLiteral
        . Common.getStringLiteral
        <$> stringLiteralGen

existsGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Exists level Variable child)
existsGen = existsForallGen Common.Exists

floorGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Floor level child)
floorGen = ceilFloorGen Common.Floor

forallGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Forall level Variable child)
forallGen = existsForallGen Common.Forall

iffGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Iff level child)
iffGen = binaryOperatorGen Common.Iff

impliesGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Implies level child)
impliesGen = binaryOperatorGen Common.Implies

inGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (In level child)
inGen = equalsInGen Common.In

nextGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Next level child)
nextGen = unaryOperatorGen Common.Next

notGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Not level child)
notGen = unaryOperatorGen Common.Not

orGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Or level child)
orGen = binaryOperatorGen Common.Or

rewritesGen
    :: (Sort level -> Gen child)
    -> Sort level
    -> Gen (Rewrites level child)
rewritesGen = binaryOperatorGen Common.Rewrites

topGen :: Sort level -> Gen (Top level child)
topGen = topBottomGen Common.Top

patternGen
    :: MetaOrObject level
    => (Sort level -> Gen child)
    -> Sort level
    -> Gen (Common.Pattern level dom Variable child)
patternGen childGen patternSort =
    Gen.frequency
        [ (1, Common.AndPattern <$> andGen childGen patternSort)
        , (1, Common.ApplicationPattern <$> applicationGen childGen patternSort)
        , (1, Common.BottomPattern <$> bottomGen patternSort)
        , (1, Common.CeilPattern <$> ceilGen childGen patternSort)
        , (1, Common.EqualsPattern <$> equalsGen childGen patternSort)
        , (1, Common.ExistsPattern <$> existsGen childGen patternSort)
        , (1, Common.FloorPattern <$> floorGen childGen patternSort)
        , (1, Common.ForallPattern <$> forallGen childGen patternSort)
        , (1, Common.IffPattern <$> iffGen childGen patternSort)
        , (1, Common.ImpliesPattern <$> impliesGen childGen patternSort)
        , (1, Common.InPattern <$> inGen childGen patternSort)
        , (1, Common.NotPattern <$> notGen childGen patternSort)
        , (1, Common.OrPattern <$> orGen childGen patternSort)
        , (1, Common.TopPattern <$> topGen patternSort)
        , (5, Common.VariablePattern <$> variableGen patternSort)
        ]

termLikeGen
    :: MetaOrObject level
    => Hedgehog.Gen (TermLike Variable)
termLikeGen = standaloneGen (termLikeChildGen =<< sortGen)

termLikeChildGen
    :: MetaOrObject level
    => Sort level
    -> Gen (TermLike Variable)
termLikeChildGen patternSort =
    Gen.sized termLikeChildGenWorker
  where
    termLikeChildGenWorker n
      | n <= 1 =
        case isMetaOrObject patternSort of
            IsObject
              | patternSort == stringMetaSort ->
                mkStringLiteral . Common.getStringLiteral <$> stringLiteralGen
              | patternSort == charMetaSort ->
                mkCharLiteral . Common.getCharLiteral <$> charLiteralGen
              | otherwise ->
                Gen.choice
                    [ mkVar <$> variableGen patternSort
                    , mkDomainValue <$> genBuiltin patternSort
                    ]
      | otherwise =
        (Gen.small . Gen.frequency)
            [ (1, termLikeAndGen)
            , (1, termLikeAppGen)
            , (1, termLikeBottomGen)
            , (1, termLikeCeilGen)
            , (1, termLikeEqualsGen)
            , (1, termLikeExistsGen)
            , (1, termLikeFloorGen)
            , (1, termLikeForallGen)
            , (1, termLikeIffGen)
            , (1, termLikeImpliesGen)
            , (1, termLikeInGen)
            , (1, termLikeNotGen)
            , (1, termLikeOrGen)
            , (1, termLikeTopGen)
            , (5, termLikeVariableGen)
            ]
    termLikeAndGen =
        mkAnd
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeAppGen =
        mkApp patternSort
            <$> symbolOrAliasGen
            <*> couple (termLikeChildGen =<< sortGen)
    termLikeBottomGen = pure (mkBottom patternSort)
    termLikeCeilGen = do
        child <- termLikeChildGen =<< sortGen
        pure (mkCeil patternSort child)
    termLikeEqualsGen = do
        operandSort <- sortGen
        mkEquals patternSort
            <$> termLikeChildGen operandSort
            <*> termLikeChildGen operandSort
    termLikeExistsGen = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (termLikeChildGen patternSort)
        pure (mkExists var child)
    termLikeForallGen = do
        varSort <- sortGen
        var <- variableGen varSort
        child <-
            Reader.local
                (addVariable var)
                (termLikeChildGen patternSort)
        pure (mkForall var child)
    termLikeFloorGen = do
        child <- termLikeChildGen =<< sortGen
        pure (mkFloor patternSort child)
    termLikeIffGen =
        mkIff
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeImpliesGen =
        mkImplies
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeInGen =
        mkIn patternSort
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeNotGen =
        mkNot <$> termLikeChildGen patternSort
    termLikeOrGen =
        mkOr
            <$> termLikeChildGen patternSort
            <*> termLikeChildGen patternSort
    termLikeTopGen = pure (mkTop patternSort)
    termLikeVariableGen = mkVar <$> variableGen patternSort

korePatternGen :: Hedgehog.Gen ParsedPattern
korePatternGen =
    standaloneGen (korePatternChildGen =<< sortGen)

korePatternChildGen
    ::  forall level.
        MetaOrObject level
    => Sort level
    -> Gen ParsedPattern
korePatternChildGen patternSort' =
    Gen.sized korePatternChildGenWorker
  where
    korePatternChildGenWorker n
      | n <= 1 =
        case isMetaOrObject patternSort' of
            IsObject
              | patternSort' == stringMetaSort ->
                korePatternGenStringLiteral
              | patternSort' == charMetaSort ->
                korePatternGenCharLiteral
              | otherwise ->
                Gen.choice [korePatternGenVariable, korePatternGenDomainValue]
      | otherwise =
        case isMetaOrObject patternSort' of
            IsObject ->
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
        asParsedPattern . Common.StringLiteralPattern <$> stringLiteralGen

    korePatternGenCharLiteral :: Gen ParsedPattern
    korePatternGenCharLiteral =
        asParsedPattern . Common.CharLiteralPattern <$> charLiteralGen

    korePatternGenDomainValue :: level ~ Object => Gen ParsedPattern
    korePatternGenDomainValue =
        asParsedPattern . Common.DomainValuePattern
            <$> genBuiltinExternal patternSort'

    korePatternGenNext :: level ~ Object => Gen ParsedPattern
    korePatternGenNext =
        asParsedPattern . Common.NextPattern
            <$> nextGen korePatternChildGen patternSort'

    korePatternGenRewrites :: level ~ Object => Gen ParsedPattern
    korePatternGenRewrites =
        asParsedPattern . Common.RewritesPattern
            <$> rewritesGen korePatternChildGen patternSort'

    korePatternGenVariable :: Gen ParsedPattern
    korePatternGenVariable =
        asParsedPattern . Common.VariablePattern <$> variableGen patternSort'

korePatternUnifiedGen :: Gen ParsedPattern
korePatternUnifiedGen = korePatternChildGen =<< sortGen

predicateGen
    :: MetaOrObject level
    => Gen (TermLike Variable)
    -> Hedgehog.Gen (Syntax.Predicate Variable)
predicateGen childGen = standaloneGen (predicateChildGen childGen =<< sortGen)

predicateChildGen
    :: MetaOrObject level
    => Gen (TermLike Variable)
    -> Sort level
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
    predicateChildGenNot = do
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
    :: (Sort Object -> Gen patternType)
    -> Gen (SentenceAlias Object patternType)
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
                    Common.Application
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
   :: Gen patternType
   -> Gen (SentenceAxiom SortVariable patternType)
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

koreSentenceGen :: Gen ParsedSentence
koreSentenceGen =
    Gen.choice
        [ SentenceAliasSentence <$> sentenceAliasGen korePatternChildGen
        , SentenceSymbolSentence <$> sentenceSymbolGen
        , SentenceImportSentence
            <$> sentenceImportGen
        , SentenceAxiomSentence <$> sentenceAxiomGen korePatternUnifiedGen
        , SentenceClaimSentence <$> sentenceAxiomGen korePatternUnifiedGen
        , SentenceSortSentence <$> sentenceSortGen
        , (SentenceHookSentence . SentenceHookedSort) <$> sentenceSortGen
        , (SentenceHookSentence . SentenceHookedSymbol) <$> sentenceSymbolGen
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

sortVariableSort :: Text -> Sort level
sortVariableSort name =
    SortVariableSort (sortVariable name)

sortActual :: Text -> [Sort level] -> Sort level
sortActual name sorts =
    SortActualSort SortActual
        { sortActualName = testId name
        , sortActualSorts = sorts
        }

expandedPatternGen :: MetaOrObject level => Gen (Pattern Object Variable)
expandedPatternGen =
    Pattern.fromTermLike <$> (termLikeChildGen =<< sortGen)

orPatternGen :: Gen (OrPattern Object Variable)
orPatternGen =
    OrPattern.fromPatterns <$> Gen.list (Range.linear 0 64) expandedPatternGen
