{-# LANGUAGE Strict #-}

module Test.ConsistentKore (
    CollectionSorts (..),
    Setup (..),
    runTermGen,
    termLikeGen,
) where

import Prelude.Kore

import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Control.Arrow as Arrow
import qualified Control.Monad as Monad
import Control.Monad.Reader (
    ReaderT,
 )
import qualified Control.Monad.Reader as Reader
import qualified Data.Functor.Foldable as Recursive
import qualified Data.List as List (
    foldl',
 )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Text (
    Text,
 )

import qualified Kore.Attribute.Constructor as Attribute.Constructor (
    Constructor (..),
 )
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    freeVariables,
    nullFreeVariables,
 )
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Attribute.Symbol as Attribute.Symbol (
    Symbol (..),
 )
import Kore.Builtin.AssociativeCommutative as AssociativeCommutative (
    TermWrapper,
    asInternal,
 )
import qualified Kore.Builtin.Bool.Bool as BuiltinBool (
    asBuiltin,
 )
import qualified Kore.Builtin.Int.Int as BuiltinInt (
    asBuiltin,
 )
import qualified Kore.Builtin.List.List as BuiltinList (
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
import qualified Kore.Internal.Alias as Alias.DoNotUse
import qualified Kore.Internal.Alias as Internal (
    Alias (Alias),
 )
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (ApplicationSorts),
 )
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.InternalString
import qualified Kore.Internal.Symbol as Internal (
    Symbol (Symbol),
 )
import qualified Kore.Internal.Symbol as Symbol.DoNotUse
import Kore.Internal.TermLike (
    Key,
    TermLike,
    TermLikeF (..),
    mkAnd,
    mkApplyAlias,
    mkApplySymbol,
    mkBottom,
    mkCeil,
    mkElemVar,
    mkEquals,
    mkEvaluated,
    mkExists,
    mkFloor,
    mkForall,
    mkIff,
    mkImplies,
    mkIn,
    mkInternalBool,
    mkInternalInt,
    mkInternalList,
    mkInternalString,
    mkMu,
    mkNot,
    mkNu,
    mkOr,
    mkRewrites,
    mkSetVar,
    mkStringLiteral,
    mkTop,
    retractKey,
 )
import qualified Kore.Internal.TermLike as TermLike (
    asConcrete,
 )
import Kore.Sort (
    Sort,
 )
import Kore.Syntax.Variable

import Test.Kore (
    idGen,
 )

data SortRequirements
    = AnySort
    | SpecificSort !Sort
    deriving (Eq, Ord, Show)

data AttributeRequirements = AttributeRequirements
    { isConstructorLike :: !Bool
    , isConcrete :: !Bool
    }
    deriving (Eq, Ord, Show)

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
    { availableElementVariables :: !(Set.Set (ElementVariable VariableName))
    , availableSetVariables :: !(Set.Set (SetVariable VariableName))
    , onlyConstructorLike :: !Bool
    , onlyConcrete :: !Bool
    }
    deriving (Eq, Ord, Show)

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

runTermGen :: Setup -> Gen a -> Hedgehog.Gen a
runTermGen
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
                }

addQuantifiedSetVariable :: SetVariable VariableName -> Context -> Context
addQuantifiedSetVariable
    variable
    context@Context{availableSetVariables} =
        context{availableSetVariables = Set.insert variable availableSetVariables}

addQuantifiedElementVariable :: ElementVariable VariableName -> Context -> Context
addQuantifiedElementVariable
    variable
    context@Context{availableElementVariables} =
        context
            { availableElementVariables =
                Set.insert variable availableElementVariables
            }

localContext :: (Context -> Context) -> Gen a -> Gen a
localContext transformer =
    Reader.local (Arrow.second transformer)

requestConstructorLike :: Gen a -> Gen a
requestConstructorLike =
    localContext (\context -> context{onlyConstructorLike = True})

requestConcrete :: Gen a -> Gen a
requestConcrete =
    localContext (\context -> context{onlyConcrete = True})

termLikeGen :: Gen (TermLike VariableName)
termLikeGen = do
    topSort <- sortGen
    maybeResult <-
        Gen.scale limitTermDepth $
            Gen.sized (\size -> termLikeGenImpl size topSort)
    case maybeResult of
        Nothing -> error "Cannot generate terms."
        Just result -> return result
  where
    limitTermDepth (Range.Size s)
        | s < 10 = Range.Size s
        | otherwise = Range.Size 10

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
    checkTermF (EvaluatedF _) = term
    checkTermF (InhabitantF _) = term -- Not implemented.
    checkTermF (EndiannessF _) = term -- Not implemented.
    checkTermF (SignednessF _) = term -- Not implemented.
    checkTermF (InjF _) = term -- Not implemented.
    checkTermF (DefinedF _) = term -- Not implemented.

termGenerators :: Gen (Map.Map SortRequirements [TermGenerator])
termGenerators = do
    (setup, Context{onlyConstructorLike}) <- Reader.ask
    generators <-
        filterGeneratorsAndGroup
            [ andGenerator
            , bottomGenerator
            , ceilGenerator
            , equalsGenerator
            , existsGenerator
            , floorGenerator
            , forallGenerator
            , iffGenerator
            , impliesGenerator
            , inGenerator
            , muGenerator
            , notGenerator
            , nuGenerator
            , orGenerator
            , rewritesGenerator
            , topGenerator
            , evaluatedGenerator
            ]
    literals <-
        filterGeneratorsAndGroup
            ( catMaybes
                [maybeStringLiteralGenerator setup]
            )
    variable <- allVariableGenerators
    symbol <- symbolGenerators
    alias <- aliasGenerators
    allBuiltin <- allBuiltinGenerators
    if onlyConstructorLike
        then return symbol
        else
            return
                ( generators
                    `merge` literals
                    `merge` wrap variable
                    `merge` symbol
                    `merge` alias
                    `merge` wrap allBuiltin
                )
  where
    merge :: Ord a => Map.Map a [b] -> Map.Map a [b] -> Map.Map a [b]
    merge = Map.unionWith (++)

    wrap :: Map.Map a b -> Map.Map a [b]
    wrap a = listSingleton <$> a

    listSingleton :: a -> [a]
    listSingleton x = [x]

withContext ::
    Monad m =>
    Context ->
    ReaderT (r, Context) m a ->
    ReaderT (r, Context) m a
withContext context = Reader.local (\(r, _) -> (r, context))

nullaryFreeSortOperatorGenerator ::
    (Sort -> TermLike VariableName) ->
    TermGenerator
nullaryFreeSortOperatorGenerator builder =
    TermGenerator
        { arity = 0
        , sort = AnySort
        , attributes =
            AttributeRequirements
                { isConstructorLike = False
                , isConcrete = True
                }
        , generator = worker
        }
  where
    worker _childGenerator resultSort =
        return (Just (builder resultSort))

unaryOperatorGenerator ::
    (TermLike VariableName -> TermLike VariableName) ->
    TermGenerator
unaryOperatorGenerator builder =
    TermGenerator
        { arity = 1
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
        child <- childGenerator childSort
        return
            (builder <$> child) -- Maybe functor

unaryFreeSortOperatorGenerator ::
    (Sort -> TermLike VariableName -> TermLike VariableName) ->
    TermGenerator
unaryFreeSortOperatorGenerator builder =
    TermGenerator
        { arity = 1
        , sort = AnySort
        , attributes =
            AttributeRequirements
                { isConstructorLike = False
                , isConcrete = True
                }
        , generator = worker
        }
  where
    worker childGenerator resultSort = do
        childSort <- sortGen
        child <- childGenerator childSort
        return
            (builder resultSort <$> child) -- Maybe functor

unaryQuantifiedElementOperatorGenerator ::
    (ElementVariable VariableName -> TermLike VariableName -> TermLike VariableName) ->
    TermGenerator
unaryQuantifiedElementOperatorGenerator builder =
    TermGenerator
        { arity = 1
        , sort = AnySort
        , attributes =
            AttributeRequirements
                { isConstructorLike = False
                , isConcrete = False
                }
        , generator = worker
        }
  where
    worker childGenerator childSort = do
        (_, context) <- Reader.ask
        variableSort <- sortGen
        quantifiedVariable <- elementVariableGen variableSort
        child <-
            withContext
                (addQuantifiedElementVariable quantifiedVariable context)
                $ childGenerator childSort
        return
            (builder quantifiedVariable <$> child) -- Maybe functor

muNuOperatorGenerator ::
    (SetVariable VariableName -> TermLike VariableName -> TermLike VariableName) ->
    TermGenerator
muNuOperatorGenerator builder =
    TermGenerator
        { arity = 1
        , sort = AnySort
        , attributes =
            AttributeRequirements
                { isConstructorLike = False
                , isConcrete = False
                }
        , generator = worker
        }
  where
    worker childGenerator childSort = do
        (_, context) <- Reader.ask
        quantifiedVariable <- setVariableGen childSort
        withContext (addQuantifiedSetVariable quantifiedVariable context) $ do
            child <- childGenerator childSort
            return
                (builder quantifiedVariable <$> child) -- Maybe functor

binaryFreeSortOperatorGenerator ::
    (Sort -> TermLike VariableName -> TermLike VariableName -> TermLike VariableName) ->
    TermGenerator
binaryFreeSortOperatorGenerator builder =
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
    worker childGenerator resultSort = do
        childSort <- sortGen
        child1 <- childGenerator childSort
        child2 <- childGenerator childSort
        return
            (builder resultSort <$> child1 <*> child2) -- Maybe applicative

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

bottomGenerator :: TermGenerator
bottomGenerator = nullaryFreeSortOperatorGenerator mkBottom

ceilGenerator :: TermGenerator
ceilGenerator = unaryFreeSortOperatorGenerator mkCeil

equalsGenerator :: TermGenerator
equalsGenerator = binaryFreeSortOperatorGenerator mkEquals

existsGenerator :: TermGenerator
existsGenerator = unaryQuantifiedElementOperatorGenerator mkExists

floorGenerator :: TermGenerator
floorGenerator = unaryFreeSortOperatorGenerator mkFloor

forallGenerator :: TermGenerator
forallGenerator = unaryQuantifiedElementOperatorGenerator mkForall

iffGenerator :: TermGenerator
iffGenerator = binaryOperatorGenerator mkIff

impliesGenerator :: TermGenerator
impliesGenerator = binaryOperatorGenerator mkImplies

inGenerator :: TermGenerator
inGenerator = binaryFreeSortOperatorGenerator mkIn

muGenerator :: TermGenerator
muGenerator = muNuOperatorGenerator mkMu

notGenerator :: TermGenerator
notGenerator = unaryOperatorGenerator mkNot

nuGenerator :: TermGenerator
nuGenerator = muNuOperatorGenerator mkNu

orGenerator :: TermGenerator
orGenerator = binaryOperatorGenerator mkOr

rewritesGenerator :: TermGenerator
rewritesGenerator = binaryOperatorGenerator mkRewrites

topGenerator :: TermGenerator
topGenerator = nullaryFreeSortOperatorGenerator mkTop

evaluatedGenerator :: TermGenerator
evaluatedGenerator = unaryOperatorGenerator mkEvaluated

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
            Map.fromList
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
            let request =
                    if BuiltinMap.isSymbolElement symbol
                        || BuiltinSet.isSymbolElement symbol
                        then requestConcrete . requestConstructorLike
                        else -- TODO (virgil): also allow constructor-like stuff
                        -- with variables.
                            id
            maybeTerms <- request $ mapM termGenerator applicationSortsOperands
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
filterGenerators = Monad.filterM acceptGenerator
  where
    acceptGenerator :: TermGenerator -> Gen Bool
    acceptGenerator
        TermGenerator{attributes} =
            do
                (_, context@(Context _ _ _ _)) <- Reader.ask
                let Context{onlyConcrete, onlyConstructorLike} = context
                return $ case attributes of
                    AttributeRequirements{isConcrete, isConstructorLike} ->
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

setVariableGen :: Sort -> Gen (SetVariable VariableName)
setVariableGen sort = (fmap . fmap) SetVariableName (variableGen sort)

elementVariableGen :: Sort -> Gen (ElementVariable VariableName)
elementVariableGen sort = (fmap . fmap) ElementVariableName (variableGen sort)

variableGen :: Sort -> Gen (Variable VariableName)
variableGen variableSort = do
    base <- idGen
    let variableName = VariableName{base, counter = mempty}
    return Variable{variableName, variableSort}
