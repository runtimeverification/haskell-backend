module Test.ConsistentKore (
    CollectionSorts (..),
    MapSorts (..),
    Setup (..),
    runKoreGen,
    patternGen,
    -- testing only
    termLikeGenWithSort,
) where

import Control.Arrow qualified as Arrow
import Control.Monad.Reader (
    ReaderT,
 )
import Control.Monad.Reader qualified as Reader
import Data.Functor.Foldable qualified as Recursive
import Data.HashMap.Strict qualified as HashMap
import Data.List qualified as List (
    foldl',
 )
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (
    Text,
 )
import Hedgehog qualified
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Kore.Attribute.Constructor qualified as Attribute.Constructor (
    Constructor (..),
 )
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    freeVariables,
    nullFreeVariables,
 )
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.Attribute.Symbol qualified as Attribute.Symbol (
    Symbol (..),
    isFunction,
 )
import Kore.Builtin.AssociativeCommutative as AssociativeCommutative (
    TermWrapper,
    asInternal,
 )
import Kore.Builtin.Bool.Bool qualified as BuiltinBool (
    asBuiltin,
 )
import Kore.Builtin.Int.Int qualified as BuiltinInt (
    asBuiltin,
 )
import Kore.Builtin.List.List qualified as BuiltinList (
    asBuiltin,
 )
import Kore.Builtin.Map.Map as BuiltinMap (
    isSymbolElement,
 )
import Kore.Builtin.Set.Set as BuiltinSet (
    isSymbolElement,
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.Alias qualified as Alias.DoNotUse
import Kore.Internal.Alias qualified as Internal (
    Alias (Alias),
 )
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (ApplicationSorts),
 )
import Kore.Internal.From
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.InternalString
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (Predicate)
import Kore.Internal.Symbol qualified as Internal (
    Symbol (Symbol),
 )
import Kore.Internal.Symbol qualified as Symbol.DoNotUse
import Kore.Internal.TermLike (
    Key,
    TermLike,
    TermLikeF (..),
    mkAnd,
    mkApplyAlias,
    mkApplySymbol,
    mkElemVar,
    mkInternalBool,
    mkInternalInt,
    mkInternalList,
    mkInternalString,
    mkOr,
    mkSetVar,
    mkStringLiteral,
    retractKey,
 )
import Kore.Internal.TermLike qualified as TermLike (
    asConcrete,
 )
import Kore.Sort (
    Sort,
 )
import Kore.Syntax.Variable
import Prelude.Kore
import Test.Kore (
    idGen,
 )

data SortRequirements
    = AnySort
    | SpecificSort !Sort
    deriving stock (Eq, Ord, Show)

data AttributeRequirements = AttributeRequirements
    { isConstructorLike :: !Bool
    , isConcrete :: !Bool
    }
    deriving stock (Eq, Ord, Show)

data TermGenerator = TermGenerator
    { arity :: !Integer
    , sort :: !SortRequirements
    , attributes :: !AttributeRequirements
    , generator ::
        (Sort -> Gen (Maybe (TermLike VariableName))) ->
        Sort ->
        Gen (Maybe (TermLike VariableName))
    }

termGeneratorSort :: TermGenerator -> SortRequirements
termGeneratorSort TermGenerator{sort} = sort

data BuiltinGenerator = BuiltinGenerator
    { arity :: !Integer
    , sort :: !SortRequirements
    , attributes :: !AttributeRequirements
    , generator ::
        (Sort -> Gen (Maybe (TermLike VariableName))) ->
        Gen (Maybe (TermLike VariableName))
    }

data CollectionSorts = CollectionSorts
    { collectionSort :: !Sort
    , elementSort :: !Sort
    }

data MapSorts = MapSorts
    { collectionSort :: !Sort
    , keySort :: !Sort
    , valueSort :: !Sort
    }

data Context = Context
    { availableElementVariables :: (Set.Set (ElementVariable VariableName))
    , availableSetVariables :: (Set.Set (SetVariable VariableName))
    , onlyConstructorLike :: Bool
    , onlyConcrete :: Bool
    , allowTermConnectives :: Bool
    }
    deriving stock (Eq, Ord, Show)

data Setup = Setup
    { allSorts :: ![Sort]
    , allSymbols :: ![Internal.Symbol]
    , allAliases :: ![Internal.Alias (TermLike VariableName)]
    , freeElementVariables :: !(Set.Set (ElementVariable VariableName))
    , freeSetVariables :: !(Set.Set (SetVariable VariableName))
    , maybeIntSort :: !(Maybe Sort)
    , maybeBoolSort :: !(Maybe Sort)
    , maybeListSorts :: !(Maybe CollectionSorts)
    , maybeMapSorts :: !(Maybe MapSorts)
    , maybeSetSorts :: !(Maybe CollectionSorts)
    , maybeStringLiteralSort :: !(Maybe Sort)
    , maybeStringBuiltinSort :: !(Maybe Sort)
    , metadataTools :: SmtMetadataTools Attribute.Symbol
    }

type Gen = ReaderT (Setup, Context) Hedgehog.Gen

runKoreGen :: Setup -> Gen a -> Hedgehog.Gen a
runKoreGen
    setup@Setup{freeElementVariables, freeSetVariables}
    generator =
        Reader.runReaderT generator (setup, context)
      where
        context =
            Context
                { availableElementVariables = freeElementVariables
                , availableSetVariables = freeSetVariables
                , onlyConstructorLike = False
                , onlyConcrete = False
                , allowTermConnectives = True
                }

patternGen :: Gen (Pattern VariableName)
patternGen =
    Pattern.fromTermAndPredicate
        <$> termGen
        <*> predicateGen

localContext :: (Context -> Context) -> Gen a -> Gen a
localContext transformer =
    Reader.local (Arrow.second transformer)

requestConstructorLike :: Gen a -> Gen a
requestConstructorLike =
    localContext (\context -> context{onlyConstructorLike = True})

requestConcrete :: Gen a -> Gen a
requestConcrete =
    localContext (\context -> context{onlyConcrete = True})

withoutConnectives :: Gen a -> Gen a
withoutConnectives =
    localContext (\context -> context{allowTermConnectives = False})

termGen :: Gen (TermLike VariableName)
termGen =
    sortGen >>= termLikeGenWithSort

termLikeGenWithSort :: Sort -> Gen (TermLike VariableName)
termLikeGenWithSort topSort = do
    maybeResult <-
        Gen.scale limitTermDepth $
            Gen.sized (\size -> termLikeGenImpl size topSort)
    case maybeResult of
        Nothing -> error $ "Cannot generate terms for " <> show topSort
        Just result -> return result
  where
    limitTermDepth (Range.Size s)
        | s < 10 = Range.Size s
        | otherwise = Range.Size 10

predicateGen :: Gen (Predicate VariableName)
predicateGen =
    Gen.recursive
        Gen.choice
        [ return fromTop_
        , return fromBottom_
        ]
        [ andPredicateGen
        , orPredicateGen
        , notPredicateGen
        , impliesPredicateGen
        , iffPredicateGen
        , ceilGen
        , floorGen
        , equalsGen
        , inGen
        , existsPredicateGen
        , forallPredicateGen
        ]

andPredicateGen :: Gen (Predicate VariableName)
andPredicateGen =
    Gen.subterm2 predicateGen predicateGen fromAnd

orPredicateGen :: Gen (Predicate VariableName)
orPredicateGen =
    Gen.subterm2 predicateGen predicateGen fromOr

impliesPredicateGen :: Gen (Predicate VariableName)
impliesPredicateGen =
    Gen.subterm2 predicateGen predicateGen fromImplies

iffPredicateGen :: Gen (Predicate VariableName)
iffPredicateGen =
    Gen.subterm2 predicateGen predicateGen fromIff

notPredicateGen :: Gen (Predicate VariableName)
notPredicateGen =
    Gen.subterm predicateGen fromNot

ceilGen :: Gen (Predicate VariableName)
ceilGen =
    fromCeil_ <$> withoutConnectives termGen

floorGen :: Gen (Predicate VariableName)
floorGen =
    fromFloor_ <$> withoutConnectives termGen

equalsGen :: Gen (Predicate VariableName)
equalsGen = withoutConnectives $ do
    sort' <- sortGen
    fromEquals_
        <$> termLikeGenWithSort sort'
        <*> termLikeGenWithSort sort'

inGen :: Gen (Predicate VariableName)
inGen = withoutConnectives $ do
    sort' <- sortGen
    fromIn_
        <$> termLikeGenWithSort sort'
        <*> termLikeGenWithSort sort'

existsPredicateGen :: Gen (Predicate VariableName)
existsPredicateGen = do
    sort' <- sortGen
    variable <- elementVariableGen sort'
    Gen.subterm predicateGen (fromExists variable)

forallPredicateGen :: Gen (Predicate VariableName)
forallPredicateGen = do
    sort' <- sortGen
    variable <- elementVariableGen sort'
    Gen.subterm predicateGen (fromForall variable)

termLikeGenImpl :: Range.Size -> Sort -> Gen (Maybe (TermLike VariableName))
termLikeGenImpl (Range.Size size) requestedSort = do
    allGenerators <- termGenerators
    let allSortGenerators :: [TermGenerator]
        allSortGenerators = generatorsForSort allGenerators requestedSort

        nullaryGenerators :: [TermGenerator]
        nullaryGenerators = filter isNullary allSortGenerators

        actualGenerators :: [TermGenerator]
        actualGenerators =
            if size == 0 then nullaryGenerators else allSortGenerators

        nextGenerator :: Sort -> Gen (Maybe (TermLike VariableName))
        nextGenerator =
            if size > 0
                then termLikeGenImpl (Range.Size $ size - 1)
                else const empty
    if null actualGenerators
        then return Nothing
        else do
            TermGenerator{generator} <- Gen.element actualGenerators
            tryToGetJust 3 (generator nextGenerator requestedSort)
  where
    isNullary :: TermGenerator -> Bool
    isNullary TermGenerator{arity} = arity == 0

    tryToGetJust ::
        Int ->
        Gen (Maybe a) ->
        Gen (Maybe a)
    tryToGetJust attempts generator
        | attempts <= 0 = return Nothing
        | otherwise = do
            maybeResult <- generator
            maybe
                (tryToGetJust (attempts - 1) generator)
                (return . Just)
                maybeResult

    generatorsForSort ::
        Map.Map SortRequirements [TermGenerator] -> Sort -> [TermGenerator]
    generatorsForSort generators sort =
        fromMaybe [] (Map.lookup AnySort generators)
            ++ fromMaybe [] (Map.lookup (SpecificSort sort) generators)

{- The only purpose of this function is to produce an error message when
new cases are being added to TermLikeF, so that we don't forget to also
change this file.
-}
_checkTermImplemented :: TermLike VariableName -> TermLike VariableName
_checkTermImplemented term@(Recursive.project -> _ :< termF) =
    checkTermF termF
  where
    checkTermF (AndF _) = term
    checkTermF (ApplySymbolF _) = term
    checkTermF (ApplyAliasF _) = term
    checkTermF (BottomF _) = term
    checkTermF (CeilF _) = term
    checkTermF (DomainValueF _) = term
    checkTermF (EqualsF _) = term
    checkTermF (ExistsF _) = term
    checkTermF (FloorF _) = term
    checkTermF (ForallF _) = term
    checkTermF (IffF _) = term
    checkTermF (ImpliesF _) = term
    checkTermF (InF _) = term
    checkTermF (MuF _) = term
    checkTermF (NextF _) = term
    checkTermF (NotF _) = term
    checkTermF (NuF _) = term
    checkTermF (OrF _) = term
    checkTermF (RewritesF _) = term
    checkTermF (TopF _) = term
    checkTermF (VariableF _) = term
    checkTermF (StringLiteralF _) = term
    checkTermF (InternalBoolF _) = term
    checkTermF (InternalBytesF _) = term
    checkTermF (InternalIntF _) = term
    checkTermF (InternalStringF _) = term
    checkTermF (InternalListF _) = term
    checkTermF (InternalMapF _) = term
    checkTermF (InternalSetF _) = term
    checkTermF (InhabitantF _) = term -- Not implemented.
    checkTermF (EndiannessF _) = term -- Not implemented.
    checkTermF (SignednessF _) = term -- Not implemented.
    checkTermF (InjF _) = term -- Not implemented.

termGenerators :: Gen (Map.Map SortRequirements [TermGenerator])
termGenerators = do
    (setup, Context{onlyConstructorLike, allowTermConnectives}) <- Reader.ask
    connectives <-
        if allowTermConnectives
            then filterGeneratorsAndGroup [andGenerator, orGenerator]
            else pure Map.empty
    literals <-
        filterGeneratorsAndGroup
            ( catMaybes
                [maybeStringLiteralGenerator setup]
            )
    variable <- Map.map (: []) <$> allVariableGenerators
    symbol <- symbolGenerators
    alias <- aliasGenerators
    allBuiltin <- Map.map (: []) <$> allBuiltinGenerators
    if onlyConstructorLike
        then return symbol
        else
            return $
                Map.unionsWith
                    (<>)
                    [ symbol
                    , alias
                    , literals
                    , variable
                    , allBuiltin
                    , connectives
                    ]

binaryOperatorGenerator ::
    (TermLike VariableName -> TermLike VariableName -> TermLike VariableName) ->
    TermGenerator
binaryOperatorGenerator builder =
    TermGenerator
        { arity = 2
        , sort = AnySort
        , attributes =
            AttributeRequirements
                { isConstructorLike = False
                , isConcrete = True
                }
        , generator = worker
        }
  where
    worker childGenerator childSort = do
        first <- childGenerator childSort
        second <- childGenerator childSort
        return
            (builder <$> first <*> second) -- Maybe applicative

andGenerator :: TermGenerator
andGenerator = binaryOperatorGenerator mkAnd

orGenerator :: TermGenerator
orGenerator = binaryOperatorGenerator mkOr

maybeStringLiteralGenerator :: Setup -> Maybe TermGenerator
maybeStringLiteralGenerator Setup{maybeStringLiteralSort} =
    case maybeStringLiteralSort of
        Nothing -> Nothing
        Just stringSort ->
            Just
                TermGenerator
                    { arity = 0
                    , sort = SpecificSort stringSort
                    , attributes =
                        AttributeRequirements
                            { isConstructorLike = True
                            , isConcrete = True
                            }
                    , generator = \_childGenerator resultSort -> do
                        str <- stringGen
                        when
                            (stringSort /= resultSort)
                            (error "Sort mismatch.")
                        return (Just (mkStringLiteral str))
                    }

allBuiltinGenerators :: Gen (Map.Map SortRequirements TermGenerator)
allBuiltinGenerators = do
    (setup, _) <- Reader.ask
    let maybeBuiltinGenerators =
            [ maybeBoolBuiltinGenerator setup
            , maybeIntBuiltinGenerator setup
            , maybeListBuiltinGenerator setup
            , maybeMapBuiltinGenerator setup
            , maybeSetBuiltinGenerator setup
            , maybeStringBuiltinGenerator setup
            ]
        termGeneratorList =
            map toTermGenerator $ catMaybes maybeBuiltinGenerators
    filterGeneratorsGroupAndPickOne termGeneratorList
  where
    toTermGenerator :: BuiltinGenerator -> TermGenerator
    toTermGenerator
        BuiltinGenerator{arity, sort, attributes, generator} =
            TermGenerator
                { arity
                , sort
                , attributes
                , generator =
                    \childGenerator resultSort -> do
                        case sort of
                            AnySort -> return ()
                            SpecificSort generatedSort ->
                                when
                                    (generatedSort /= resultSort)
                                    (error "Sort mismatch.")
                        generator childGenerator
                }

maybeStringBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeStringBuiltinGenerator Setup{maybeStringBuiltinSort} =
    case maybeStringBuiltinSort of
        Nothing -> Nothing
        Just stringSort ->
            Just
                BuiltinGenerator
                    { arity = 0
                    , sort = SpecificSort stringSort
                    , attributes =
                        AttributeRequirements
                            { isConstructorLike = True
                            , isConcrete = True
                            }
                    , generator = stringGenerator stringSort
                    }
  where
    stringGenerator ::
        Sort ->
        (Sort -> Gen (Maybe (TermLike VariableName))) ->
        Gen (Maybe (TermLike VariableName))
    stringGenerator stringSort _childGenerator =
        Just . mkInternalString . InternalString stringSort <$> stringGen

maybeBoolBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeBoolBuiltinGenerator Setup{maybeBoolSort} =
    case maybeBoolSort of
        Nothing -> Nothing
        Just boolSort ->
            Just
                BuiltinGenerator
                    { arity = 0
                    , sort = SpecificSort boolSort
                    , attributes =
                        AttributeRequirements
                            { isConstructorLike = True
                            , isConcrete = True
                            }
                    , generator = boolGenerator boolSort
                    }
  where
    boolGenerator ::
        Sort ->
        (Sort -> Gen (Maybe (TermLike VariableName))) ->
        Gen (Maybe (TermLike VariableName))
    boolGenerator boolSort _childGenerator =
        Just . mkInternalBool . BuiltinBool.asBuiltin boolSort <$> Gen.bool

maybeIntBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeIntBuiltinGenerator Setup{maybeIntSort} =
    case maybeIntSort of
        Nothing -> Nothing
        Just intSort ->
            Just
                BuiltinGenerator
                    { arity = 0
                    , sort = SpecificSort intSort
                    , attributes =
                        AttributeRequirements
                            { isConstructorLike = True
                            , isConcrete = True
                            }
                    , generator = intGenerator intSort
                    }
  where
    intGenerator ::
        Sort ->
        (Sort -> Gen (Maybe (TermLike VariableName))) ->
        Gen (Maybe (TermLike VariableName))
    intGenerator intSort _childGenerator = do
        value <- Gen.integral (Range.constant 0 2000)
        (pure . Just . mkInternalInt) (BuiltinInt.asBuiltin intSort value)

maybeListBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeListBuiltinGenerator Setup{maybeListSorts} =
    case maybeListSorts of
        Nothing -> Nothing
        Just CollectionSorts{collectionSort, elementSort} ->
            Just
                BuiltinGenerator
                    { arity = 5
                    , sort = SpecificSort collectionSort
                    , attributes =
                        AttributeRequirements
                            { isConstructorLike = False
                            , -- We could generate constructor-like or concrete lists
                              -- if we wanted to.
                              isConcrete = False
                            }
                    , generator = listGenerator collectionSort elementSort
                    }
  where
    listGenerator ::
        Sort ->
        Sort ->
        (Sort -> Gen (Maybe (TermLike VariableName))) ->
        Gen (Maybe (TermLike VariableName))
    listGenerator listSort listElementSort childGenerator = do
        (Setup{metadataTools}, _) <- Reader.ask
        elements <-
            Gen.seq
                (Range.constant 0 5)
                (childGenerator listElementSort)
        return
            ( mkInternalList . BuiltinList.asBuiltin metadataTools listSort
                <$> sequenceA elements
            )

concreteTermGenerator ::
    Sort ->
    (Sort -> Gen (Maybe (TermLike VariableName))) ->
    Gen (Maybe (TermLike Concrete))
concreteTermGenerator requestedSort childGenerator = do
    maybeResult <-
        requestConcrete $
            childGenerator requestedSort
    return (forceConcrete <$> maybeResult)
  where
    forceConcrete term =
        fromMaybe
            (error "Expected concrete key.")
            (TermLike.asConcrete term)

-- TODO(virgil): Test that we are generating non-empty maps.
maybeMapBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeMapBuiltinGenerator Setup{maybeMapSorts} =
    case maybeMapSorts of
        Nothing -> Nothing
        Just MapSorts{collectionSort, keySort, valueSort} ->
            Just
                BuiltinGenerator
                    { arity = 10
                    , sort = SpecificSort collectionSort
                    , attributes =
                        AttributeRequirements
                            { isConstructorLike = False
                            , -- We could generate constructor-like or concrete maps
                              -- if we wanted to.
                              isConcrete = False
                            }
                    , generator =
                        acGenerator
                            collectionSort
                            keySort
                            (valueGenerator valueSort)
                    }
  where
    valueGenerator ::
        Sort ->
        (Sort -> Gen (Maybe (TermLike VariableName))) ->
        Gen (Maybe (MapValue (TermLike VariableName)))
    valueGenerator valueSort childGenerator = do
        maybeValue <- childGenerator valueSort
        return (MapValue <$> maybeValue)

-- TODO(virgil): Test that we are generating non-empty sets.
maybeSetBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeSetBuiltinGenerator Setup{maybeSetSorts} =
    case maybeSetSorts of
        Nothing -> Nothing
        Just CollectionSorts{collectionSort, elementSort} ->
            Just
                BuiltinGenerator
                    { arity = 10
                    , sort = SpecificSort collectionSort
                    , attributes =
                        AttributeRequirements
                            { isConstructorLike = False
                            , -- We could generate constructor-like or concrete sets
                              -- if we wanted to.
                              isConcrete = False
                            }
                    , generator =
                        acGenerator collectionSort elementSort valueGenerator
                    }
  where
    valueGenerator :: a -> Gen (Maybe (SetValue (TermLike VariableName)))
    valueGenerator _ = return (Just SetValue)

acGenerator ::
    forall normalized.
    AssociativeCommutative.TermWrapper normalized =>
    Sort ->
    Sort ->
    ( (Sort -> Gen (Maybe (TermLike VariableName))) ->
      Gen (Maybe (Value normalized (TermLike VariableName)))
    ) ->
    (Sort -> Gen (Maybe (TermLike VariableName))) ->
    Gen (Maybe (TermLike VariableName))
acGenerator mapSort keySort valueGenerator childGenerator = do
    let concreteKeyGenerator :: Gen (Maybe Key)
        concreteKeyGenerator =
            fmap (>>= retractKey) $
                requestConstructorLike $
                    concreteTermGenerator keySort childGenerator
    maybeConcreteMap <-
        Gen.map
            (Range.constant 0 5)
            ( (,)
                <$> concreteKeyGenerator
                <*> valueGenerator childGenerator
            )
    let concreteMapElem ::
            ( Maybe Key
            , Maybe (Value normalized (TermLike VariableName))
            ) ->
            Maybe (Key, Value normalized (TermLike VariableName))
        concreteMapElem (ma, mb) = (,) <$> ma <*> mb
        concreteMap =
            HashMap.fromList
                (mapMaybe concreteMapElem (Map.toList maybeConcreteMap))
    mixedKeys <-
        requestConstructorLike $
            Gen.set
                (Range.constant 0 5)
                (childGenerator keySort)
    let variableKeys :: [TermLike VariableName]
        variableKeys =
            filter
                (not . nullFreeVariables . freeVariables')
                (catMaybes (Set.toList mixedKeys))
    maybeVariablePairs <- mapM variablePair variableKeys
    let variablePairs :: [Element normalized (TermLike VariableName)]
        variablePairs = catMaybes maybeVariablePairs
    (Setup{metadataTools}, _) <- Reader.ask
    return $
        Just $
            AssociativeCommutative.asInternal
                metadataTools
                mapSort
                ( wrapAc
                    NormalizedAc
                        { elementsWithVariables = variablePairs
                        , concreteElements = concreteMap
                        , opaque = []
                        -- TODO (virgil): also fill the opaque field.
                        }
                )
  where
    freeVariables' :: TermLike VariableName -> FreeVariables VariableName
    freeVariables' = freeVariables
    variablePair ::
        TermLike VariableName ->
        Gen (Maybe (Element normalized (TermLike VariableName)))
    variablePair key = do
        maybeValue <- valueGenerator childGenerator
        return $ do
            -- maybe monad
            value <- maybeValue
            return (wrapElement (key, value))

stringGen :: Gen Text
stringGen = Gen.text (Range.linear 0 64) (Reader.lift Gen.unicode)

symbolGenerators :: Gen (Map.Map SortRequirements [TermGenerator])
symbolGenerators = do
    (Setup{allSymbols}, _) <- Reader.ask
    filterGeneratorsAndGroup (map symbolGenerator allSymbols)

symbolGenerator :: Internal.Symbol -> TermGenerator
symbolGenerator
    symbol@Internal.Symbol
        { symbolParams = []
        , symbolSorts =
            ApplicationSorts
                { applicationSortsOperands
                , applicationSortsResult
                }
        , symbolAttributes
        } =
        TermGenerator
            { arity = toInteger $ length applicationSortsOperands
            , sort = SpecificSort applicationSortsResult
            , attributes =
                AttributeRequirements
                    { isConstructorLike =
                        Attribute.Constructor.isConstructor $
                            Attribute.Symbol.constructor symbolAttributes
                    , isConcrete = True
                    }
            , generator = applicationGenerator
            }
      where
        applicationGenerator termGenerator sort = do
            when (sort /= applicationSortsResult) (error "Sort mismatch.")
            let restrict
                    | BuiltinMap.isSymbolElement symbol =
                        requestConcrete . requestConstructorLike
                    | BuiltinSet.isSymbolElement symbol =
                        requestConcrete . requestConstructorLike
                    | Attribute.Symbol.isFunction symbolAttributes =
                        withoutConnectives
                    | otherwise = id
            -- TODO (virgil): also allow constructor-like
            -- stuff with variables.
            maybeTerms <- restrict $ mapM termGenerator applicationSortsOperands
            return (mkApplySymbol symbol <$> sequenceA maybeTerms)
symbolGenerator
    Internal.Symbol
        { symbolParams = _ : _
        } =
        error "Not implemented."

aliasGenerators :: Gen (Map.Map SortRequirements [TermGenerator])
aliasGenerators = do
    (Setup{allAliases}, _) <- Reader.ask
    filterGeneratorsAndGroup (map aliasGenerator allAliases)

aliasGenerator :: Internal.Alias (TermLike VariableName) -> TermGenerator
aliasGenerator
    alias@Internal.Alias
        { aliasParams = []
        , aliasSorts =
            ApplicationSorts
                { applicationSortsOperands
                , applicationSortsResult
                }
        } =
        TermGenerator
            { arity = toInteger $ length applicationSortsOperands
            , sort = SpecificSort applicationSortsResult
            , attributes =
                AttributeRequirements
                    { isConstructorLike = False
                    , isConcrete = False
                    }
            , generator = applicationGenerator
            }
      where
        applicationGenerator ::
            (Sort -> Gen (Maybe (TermLike VariableName))) ->
            Sort ->
            Gen (Maybe (TermLike VariableName))
        applicationGenerator termGenerator sort = do
            when (sort /= applicationSortsResult) (error "Sort mismatch.")
            maybeTerms <- mapM termGenerator applicationSortsOperands
            return $ do
                terms <- sequenceA maybeTerms
                return $ mkApplyAlias alias terms
aliasGenerator
    Internal.Alias
        { aliasParams = _ : _
        } =
        error "Not implemented."

{- The only purpose of this function is to produce an error message when
new cases are being added to SomeVariable, so that we don't forget to also
change this file.
-}
_checkAllVariableImplemented ::
    SomeVariable VariableName -> SomeVariable VariableName
_checkAllVariableImplemented variable =
    case variableName variable of
        SomeVariableNameSet _ -> variable
        SomeVariableNameElement _ -> variable

allVariableGenerators :: Gen (Map.Map SortRequirements TermGenerator)
allVariableGenerators = do
    elementGenerators <- elementVariableGenerators
    setGenerators <- setVariableGenerators
    traverse
        Gen.element
        ( Map.unionWith
            (++)
            ((: []) <$> elementGenerators)
            ((: []) <$> setGenerators)
        )

elementVariableGenerators :: Gen (Map.Map SortRequirements TermGenerator)
elementVariableGenerators = do
    (_, Context{availableElementVariables}) <- Reader.ask
    let generators =
            map generatorForVariable (Set.toList availableElementVariables)
    filterGeneratorsGroupAndPickOne generators
  where
    generatorForVariable :: ElementVariable VariableName -> TermGenerator
    generatorForVariable variable =
        TermGenerator
            { arity = 0
            , sort = SpecificSort (variableSort variable)
            , attributes =
                AttributeRequirements
                    { isConstructorLike = False
                    , isConcrete = False
                    }
            , generator = variableGenerator variable
            }

    variableGenerator variable _termGenerator sort = do
        when (sort /= variableSort variable) (error "Sort mismatch.")
        return (Just (mkElemVar variable))

setVariableGenerators :: Gen (Map.Map SortRequirements TermGenerator)
setVariableGenerators = do
    (_, Context{availableSetVariables}) <- Reader.ask
    let generators = map generatorForVariable (Set.toList availableSetVariables)
    filterGeneratorsGroupAndPickOne generators
  where
    generatorForVariable :: SetVariable VariableName -> TermGenerator
    generatorForVariable variable =
        TermGenerator
            { arity = 0
            , sort = SpecificSort (variableSort variable)
            , attributes =
                AttributeRequirements
                    { isConstructorLike = False
                    , isConcrete = False
                    }
            , generator = variableGenerator variable
            }

    variableGenerator variable _termGenerator sort = do
        when (sort /= variableSort variable) (error "Sort mismatch.")
        return (Just (mkSetVar variable))

filterGeneratorsGroupAndPickOne ::
    [TermGenerator] -> Gen (Map.Map SortRequirements TermGenerator)
filterGeneratorsGroupAndPickOne generators = do
    groupedGenerators <- filterGeneratorsAndGroup generators
    traverse Gen.element groupedGenerators

filterGeneratorsAndGroup ::
    [TermGenerator] -> Gen (Map.Map SortRequirements [TermGenerator])
filterGeneratorsAndGroup generators = do
    filteredGenerators <- filterGenerators generators
    return (groupBySort filteredGenerators)

filterGenerators :: [TermGenerator] -> Gen [TermGenerator]
filterGenerators generators =
    Reader.asks snd >>= \context -> pure $ filter (accept context) generators
  where
    accept :: Context -> TermGenerator -> Bool
    accept
        Context{onlyConcrete, onlyConstructorLike}
        TermGenerator{attributes = AttributeRequirements{isConcrete, isConstructorLike}} =
            (not onlyConcrete || isConcrete)
                && (not onlyConstructorLike || isConstructorLike)

groupBySort :: [TermGenerator] -> Map.Map SortRequirements [TermGenerator]
groupBySort = groupBy termGeneratorSort

groupBy :: forall a b. Ord b => (a -> b) -> [a] -> Map.Map b [a]
groupBy keyExtractor elements =
    List.foldl' addElement Map.empty elements
  where
    addElement ::
        Map.Map b [a] ->
        a ->
        Map.Map b [a]
    addElement keyToElement element =
        Map.insertWith (++) (keyExtractor element) [element] keyToElement

sortGen :: Gen Sort
sortGen = do
    (Setup{allSorts}, _) <- Reader.ask
    Gen.element allSorts

elementVariableGen :: Sort -> Gen (ElementVariable VariableName)
elementVariableGen sort = (fmap . fmap) ElementVariableName (variableGen sort)

variableGen :: Sort -> Gen (Variable VariableName)
variableGen variableSort = do
    base <- idGen
    let variableName = VariableName{base, counter = mempty}
    return Variable{variableName, variableSort}
