module Test.ConsistentKore
    ( CollectionSorts (..)
    , Setup (..)
    , runTermGen
    , termLikeGen
    ) where

import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Comonad.Trans.Cofree
    ( CofreeF ((:<))
    )
import qualified Control.Monad as Monad
    ( when
    )
import Control.Monad.Reader
    ( ReaderT
    )
import qualified Control.Monad.Reader as Reader
import qualified Data.Functor.Foldable as Recursive
import qualified Data.List as List
    ( foldl'
    )
import qualified Data.Map as Map
import Data.Maybe
    ( catMaybes
    , fromMaybe
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin.Bool.Bool as BuiltinBool
    ( asBuiltin
    )
import qualified Kore.Builtin.Int.Int as BuiltinInt
    ( asBuiltin
    )
import qualified Kore.Builtin.List.List as BuiltinList
    ( asBuiltin
    )
import qualified Kore.Builtin.String.String as BuiltinString
    ( asBuiltin
    )
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.Internal.Alias as Internal
    ( Alias (Alias)
    )
import qualified Kore.Internal.Alias as Alias.DoNotUse
import Kore.Internal.ApplicationSorts
    ( ApplicationSorts (ApplicationSorts)
    )
import qualified Kore.Internal.Symbol as Internal
    ( Symbol (Symbol)
    )
import qualified Kore.Internal.Symbol as Symbol.DoNotUse
import Kore.Internal.TermLike
    ( TermLike
    , TermLikeF (..)
    , mkAnd
    , mkApplyAlias
    , mkApplySymbol
    , mkBottom
    , mkBuiltin
    , mkCeil
    , mkDomainValue
    , mkElemVar
    , mkEquals
    , mkEvaluated
    , mkExists
    , mkFloor
    , mkForall
    , mkIff
    , mkImplies
    , mkIn
    , mkMu
    , mkNot
    , mkNu
    , mkOr
    , mkRewrites
    , mkSetVar
    , mkStringLiteral
    , mkTop
    )
import Kore.Sort
    ( Sort
    )
import Kore.Syntax.DomainValue
    ( DomainValue (DomainValue)
    )
import qualified Kore.Syntax.DomainValue as DomainValue.DoNotUse
import Kore.Syntax.ElementVariable
    ( ElementVariable (ElementVariable)
    )
import Kore.Syntax.SetVariable
    ( SetVariable (SetVariable)
    )
import Kore.Syntax.Variable
    ( Concrete
    , Variable (Variable)
    )
import qualified Kore.Syntax.Variable as Variable.DoNotUse
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore
    ( idGen
    )

data SortRequirements
    = AnySort
    | SpecificSort !Sort
    deriving (Eq, Ord, Show)

data TermGenerator = TermGenerator
    { arity :: !Integer
    , sort :: !SortRequirements
    , generator
        :: (Sort -> Gen (TermLike Variable))
        -> Sort
        -> Gen (TermLike Variable)
    }

termGeneratorSort :: TermGenerator -> SortRequirements
termGeneratorSort TermGenerator {sort} = sort

data BuiltinGenerator = BuiltinGenerator
    { arity :: !Integer
    , sort :: !SortRequirements
    , generator
        :: (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    }

data CollectionSorts = CollectionSorts
    { collectionSort :: !Sort
    , elementSort :: !Sort
    }

data Context = Context
    { availableElementVariables :: !(Set.Set (ElementVariable Variable))
    , availableSetVariables :: !(Set.Set (SetVariable Variable))
    }

data Setup = Setup
    { allSorts :: ![Sort]
    , allSymbols :: ![Internal.Symbol]
    , allAliases :: ![Internal.Alias (TermLike Variable)]
    , freeElementVariables :: !(Set.Set (ElementVariable Variable))
    , freeSetVariables :: !(Set.Set (SetVariable Variable))
    , maybeIntSort :: !(Maybe Sort)
    , maybeBoolSort :: !(Maybe Sort)
    , maybeListSorts :: !(Maybe CollectionSorts)
    , maybeMapSorts :: !(Maybe CollectionSorts)
    , maybeSetSorts :: !(Maybe CollectionSorts)
    , maybeStringLiteralSort :: !(Maybe Sort)
    , maybeStringBuiltinSort :: !(Maybe Sort)
    , metadataTools :: SmtMetadataTools Attribute.Symbol
    }

type Gen = ReaderT (Setup, Context) Hedgehog.Gen

runTermGen :: Setup -> Gen a -> Hedgehog.Gen a
runTermGen
    setup@Setup{freeElementVariables, freeSetVariables}
    generator
  =
    Reader.runReaderT generator (setup, context)
  where
    context = Context
        { availableElementVariables = freeElementVariables
        , availableSetVariables = freeSetVariables
        }

addQuantifiedSetVariable :: SetVariable Variable -> Context -> Context
addQuantifiedSetVariable
    variable
    context@Context {availableSetVariables}
  =
    context {availableSetVariables = Set.insert variable availableSetVariables}

addQuantifiedElementVariable :: ElementVariable Variable -> Context -> Context
addQuantifiedElementVariable
    variable
    context@Context {availableElementVariables}
  =
    context
        { availableElementVariables =
            Set.insert variable availableElementVariables
        }

termLikeGen :: Gen (TermLike Variable)
termLikeGen = do
    topSort <- sortGen
    Gen.sized (\size -> termLikeGenImpl size topSort)

termLikeGenImpl :: Range.Size -> Sort -> Gen (TermLike Variable)
termLikeGenImpl (Range.Size size) requestedSort = do
    allGenerators <- termGenerators
    let allSortGenerators :: [TermGenerator]
        allSortGenerators = generatorsForSort allGenerators requestedSort

        nullaryGenerators :: [TermGenerator]
        nullaryGenerators = filter isNullary allSortGenerators

        actualGenerators :: [TermGenerator]
        actualGenerators =
            if size == 0 then nullaryGenerators else allSortGenerators

        nextGenerator :: Sort -> Gen (TermLike Variable)
        nextGenerator =
            if size > 0
                then termLikeGenImpl (Range.Size $ size - 1)
                else error "Did not expect to generate terms here."
    Monad.when (null actualGenerators) (error "Cannot generate elements.")
    TermGenerator {generator} <- Gen.element actualGenerators
    generator nextGenerator requestedSort
  where
    isNullary :: TermGenerator -> Bool
    isNullary TermGenerator {arity} = arity == 0

    generatorsForSort
        :: Map.Map SortRequirements [TermGenerator] -> Sort -> [TermGenerator]
    generatorsForSort generators sort =
        fromMaybe [] (Map.lookup AnySort generators)
        ++ fromMaybe [] (Map.lookup (SpecificSort sort) generators)

{- The only purpose of this function is to produce an error message when
new cases are being added to TermLikeF, so that we don't forget to also
change this file.
-}
_checkTermImplemented :: TermLike Variable -> TermLike Variable
_checkTermImplemented term@(Recursive.project -> _ :< termF) =
    checkTermF termF
  where
    checkTermF (AndF _) = term
    checkTermF (ApplySymbolF _) = term
    checkTermF (ApplyAliasF _) = term
    checkTermF (BottomF _) = term
    checkTermF (CeilF _) = term
    checkTermF (DomainValueF _) = term
    checkTermF (BuiltinF _) = term
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
    checkTermF (EvaluatedF _) = term
    checkTermF (InhabitantF _) = term  -- Not implemented.

termGenerators :: Gen (Map.Map SortRequirements [TermGenerator])
termGenerators = do
    (setup, _) <- Reader.ask
    let generators =
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
        literals = catMaybes
            [ maybeStringLiteralGenerator setup ]
        dv = catMaybes
            [ maybeIntDVGenerator setup
            , maybeBoolDVGenerator setup
            , maybeStringDVGenerator setup
            ]
    variable <- allVariableGenerators
    symbol <- symbolGenerators
    alias <- aliasGenerators
    allBuiltin <- allBuiltinGenerators
    return
        (       groupBySort generators
        `merge` groupBySort literals
        `merge` groupBySort dv
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

withContext
    :: Monad m
    => Context
    -> ReaderT (r, Context) m a
    -> ReaderT (r, Context) m a
withContext context = Reader.local (\(r, _) -> (r, context))

nullaryFreeSortOperatorGenerator
    :: (Sort -> TermLike Variable)
    -> TermGenerator
nullaryFreeSortOperatorGenerator builder =
    TermGenerator
        { arity = 0
        , sort = AnySort
        , generator = worker
        }
  where
    worker _childGenerator resultSort =
        return (builder resultSort)

unaryOperatorGenerator
    :: (TermLike Variable -> TermLike Variable)
    -> TermGenerator
unaryOperatorGenerator builder =
    TermGenerator
        { arity = 1
        , sort = AnySort
        , generator = worker
        }
  where
    worker childGenerator childSort =
        builder <$> childGenerator childSort

unaryFreeSortOperatorGenerator
    :: (Sort -> TermLike Variable -> TermLike Variable)
    -> TermGenerator
unaryFreeSortOperatorGenerator builder =
    TermGenerator
        { arity = 1
        , sort = AnySort
        , generator = worker
        }
  where
    worker childGenerator resultSort = do
        childSort <- sortGen
        child <- childGenerator childSort
        return (builder resultSort child)

unaryQuantifiedElementOperatorGenerator
    :: (ElementVariable Variable -> TermLike Variable -> TermLike Variable)
    -> TermGenerator
unaryQuantifiedElementOperatorGenerator builder =
    TermGenerator
        { arity = 1
        , sort = AnySort
        , generator = worker
        }
  where
    worker childGenerator childSort = do
        (_, context) <- Reader.ask
        variableSort <- sortGen
        quantifiedVariable <- elementVariableGen variableSort
        withContext (addQuantifiedElementVariable quantifiedVariable context)
            $ builder quantifiedVariable <$> childGenerator childSort

muNuOperatorGenerator
    :: (SetVariable Variable -> TermLike Variable -> TermLike Variable)
    -> TermGenerator
muNuOperatorGenerator builder =
    TermGenerator
        { arity = 1
        , sort = AnySort
        , generator = worker
        }
  where
    worker childGenerator childSort = do
        (_, context) <- Reader.ask
        quantifiedVariable <- setVariableGen childSort
        withContext (addQuantifiedSetVariable quantifiedVariable context) $ do
            child <- childGenerator childSort
            return (builder quantifiedVariable child)

binaryFreeSortOperatorGenerator
    :: (Sort -> TermLike Variable -> TermLike Variable -> TermLike Variable)
    -> TermGenerator
binaryFreeSortOperatorGenerator builder =
    TermGenerator
        { arity = 2
        , sort = AnySort
        , generator = worker
        }
  where
    worker childGenerator resultSort = do
        childSort <- sortGen
        child1 <- childGenerator childSort
        child2 <- childGenerator childSort
        return (builder resultSort child1 child2)

binaryOperatorGenerator
    :: (TermLike Variable -> TermLike Variable -> TermLike Variable)
    -> TermGenerator
binaryOperatorGenerator builder =
    TermGenerator
        { arity = 2
        , sort = AnySort
        , generator = worker
        }
  where
    worker childGenerator childSort =
        builder
            <$> childGenerator childSort
            <*> childGenerator childSort

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
maybeStringLiteralGenerator Setup {maybeStringLiteralSort} =
    case maybeStringLiteralSort of
        Nothing -> Nothing
        Just stringSort ->
            Just TermGenerator
                { arity = 0
                , sort = SpecificSort stringSort
                , generator = \_childGenerator resultSort -> do
                    str <- stringGen
                    Monad.when
                        (stringSort /= resultSort)
                        (error "Sort mismatch.")
                    return (mkStringLiteral str)
                }
{- The only purpose of this function is to produce an error message when
new cases are being added to Domain.Builtin, so that we don't forget to also
change this file.
-}
_checkAllBuiltinImplemented
    :: Domain.Builtin (TermLike Concrete) (TermLike variable)
    -> Domain.Builtin (TermLike Concrete) (TermLike variable)
_checkAllBuiltinImplemented builtin =
    case builtin of
        Domain.BuiltinBool _ -> builtin
        Domain.BuiltinInt _ -> builtin
        Domain.BuiltinList _ -> builtin
        Domain.BuiltinMap _ -> builtin
        Domain.BuiltinSet _ -> builtin
        Domain.BuiltinString _ -> builtin

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
    traverse Gen.element (groupBySort termGeneratorList)
  where
    toTermGenerator :: BuiltinGenerator -> TermGenerator
    toTermGenerator
        BuiltinGenerator {arity, sort, generator}
      = TermGenerator
            { arity
            , sort
            , generator =
                \childGenerator resultSort -> do
                    case sort of
                        AnySort -> return ()
                        SpecificSort generatedSort ->
                            Monad.when
                                (generatedSort /= resultSort)
                                (error "Sort mismatch.")
                    builtin <- generator childGenerator
                    return (mkBuiltin builtin)
            }

maybeStringBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeStringBuiltinGenerator Setup { maybeStringBuiltinSort } =
    case maybeStringBuiltinSort of
        Nothing -> Nothing
        Just stringSort ->
            Just BuiltinGenerator
                { arity = 0
                , sort = SpecificSort stringSort
                , generator = stringGenerator stringSort
                }
  where
    stringGenerator
        :: Sort
        -> (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    stringGenerator stringSort _childGenerator = do
        value <- stringGen
        return (BuiltinString.asBuiltin stringSort value)

maybeBoolBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeBoolBuiltinGenerator Setup { maybeBoolSort } =
    case maybeBoolSort of
        Nothing -> Nothing
        Just boolSort ->
            Just BuiltinGenerator
                { arity = 0
                , sort = SpecificSort boolSort
                , generator = boolGenerator boolSort
                }
  where
    boolGenerator
        :: Sort
        -> (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    boolGenerator boolSort _childGenerator = do
        value <- Gen.bool
        return (BuiltinBool.asBuiltin boolSort value)

maybeIntBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeIntBuiltinGenerator Setup { maybeIntSort } =
    case maybeIntSort of
        Nothing -> Nothing
        Just intSort ->
            Just BuiltinGenerator
                { arity = 0
                , sort = SpecificSort intSort
                , generator = intGenerator intSort
                }
  where
    intGenerator
        :: Sort
        -> (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    intGenerator intSort _childGenerator = do
        value <- Gen.integral (Range.constant 0 2000)
        return (BuiltinInt.asBuiltin intSort value)

maybeListBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeListBuiltinGenerator Setup { maybeListSorts } =
    case maybeListSorts of
        Nothing -> Nothing
        Just CollectionSorts {collectionSort, elementSort} ->
            Just BuiltinGenerator
                { arity = 5
                , sort = SpecificSort collectionSort
                , generator = listGenerator collectionSort elementSort
                }
  where
    listGenerator
        :: Sort
        -> Sort
        -> (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    listGenerator listSort listElementSort childGenerator = do
        (Setup {metadataTools}, _) <- Reader.ask
        elements <-
            Gen.seq (Range.constant 0 5)
            (childGenerator listElementSort)
        return (BuiltinList.asBuiltin metadataTools listSort elements)


maybeMapBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeMapBuiltinGenerator Setup { maybeMapSorts } =
    case maybeMapSorts of
        Nothing -> Nothing
        Just _ -> error "Not implemented yet."

maybeSetBuiltinGenerator :: Setup -> Maybe BuiltinGenerator
maybeSetBuiltinGenerator Setup { maybeSetSorts } =
    case maybeSetSorts of
        Nothing -> Nothing
        Just _ -> error "Not implemented yet."

maybeStringDVGenerator :: Setup -> Maybe TermGenerator
maybeStringDVGenerator Setup { maybeStringBuiltinSort } =
    maybeDVGenerator maybeStringBuiltinSort stringGen

stringGen :: Gen Text
stringGen = Gen.text (Range.linear 0 64) (Reader.lift Gen.unicode)

maybeIntDVGenerator :: Setup -> Maybe TermGenerator
maybeIntDVGenerator Setup { maybeIntSort } =
    maybeDVGenerator
        maybeIntSort
        (Text.pack . show <$> Gen.int (Range.constant 0 2000))

maybeBoolDVGenerator :: Setup -> Maybe TermGenerator
maybeBoolDVGenerator Setup { maybeBoolSort } =
    maybeDVGenerator maybeBoolSort (Text.pack . show <$> Gen.bool)

maybeDVGenerator
    :: Maybe Sort
    -> Gen Text
    -> Maybe TermGenerator
maybeDVGenerator maybeSort valueGenerator = do
    dvSort <- maybeSort
    return TermGenerator
        { arity = 0
        , sort = SpecificSort dvSort
        , generator = dvGenerator dvSort
        }
  where
    dvGenerator domainValueSort _childGenerator resultSort = do
        Monad.when (domainValueSort /= resultSort) (error "Sort mismatch.")
        value <- valueGenerator
        return
            (mkDomainValue DomainValue
                { domainValueSort
                , domainValueChild = mkStringLiteral value
                }
            )

symbolGenerators :: Gen (Map.Map SortRequirements [TermGenerator])
symbolGenerators = do
    (Setup {allSymbols}, _) <- Reader.ask
    return $ groupBySort (map symbolGenerator allSymbols)

symbolGenerator :: Internal.Symbol -> TermGenerator
symbolGenerator
    symbol@Internal.Symbol
        { symbolParams = []
        , symbolSorts = ApplicationSorts
            { applicationSortsOperands
            , applicationSortsResult
            }
        }
  = TermGenerator
        { arity = toInteger $ length applicationSortsOperands
        , sort = SpecificSort applicationSortsResult
        , generator = applicationGenerator
        }
  where
    applicationGenerator termGenerator sort = do
        Monad.when (sort /= applicationSortsResult) (error "Sort mismatch.")
        terms <- mapM termGenerator applicationSortsOperands
        return (mkApplySymbol symbol terms)
symbolGenerator
    Internal.Symbol
        { symbolParams = _ : _
        }
  =
    error "Not implemented."

aliasGenerators :: Gen (Map.Map SortRequirements [TermGenerator])
aliasGenerators = do
    (Setup {allAliases}, _) <- Reader.ask
    return $ groupBySort (map aliasGenerator allAliases)

aliasGenerator :: Internal.Alias (TermLike Variable) -> TermGenerator
aliasGenerator
    alias@Internal.Alias
        { aliasParams = []
        , aliasSorts = ApplicationSorts
            { applicationSortsOperands
            , applicationSortsResult
            }
        }
  = TermGenerator
        { arity = toInteger $ length applicationSortsOperands
        , sort = SpecificSort applicationSortsResult
        , generator = applicationGenerator
        }
  where
    applicationGenerator termGenerator sort = do
        Monad.when (sort /= applicationSortsResult) (error "Sort mismatch.")
        terms <- mapM termGenerator applicationSortsOperands
        return (mkApplyAlias alias terms)
aliasGenerator
    Internal.Alias
        { aliasParams = _ : _
        }
  =
    error "Not implemented."

{- The only purpose of this function is to produce an error message when
new cases are being added to UnifiedVariable, so that we don't forget to also
change this file.
-}
_checkAllVariableImplemented
    :: UnifiedVariable Variable -> UnifiedVariable Variable
_checkAllVariableImplemented variable =
    case variable of
        SetVar _ -> variable
        ElemVar _ -> variable

allVariableGenerators :: Gen (Map.Map SortRequirements TermGenerator)
allVariableGenerators = do
    elementGenerators <- elementVariableGenerators
    setGenerators <- setVariableGenerators
    traverse Gen.element
        (Map.unionWith (++)
            ((:[]) <$> elementGenerators)
            ((:[]) <$> setGenerators)
        )

elementVariableGenerators :: Gen (Map.Map SortRequirements TermGenerator)
elementVariableGenerators = do
    (_, Context {availableElementVariables}) <- Reader.ask
    let generators =
            map generatorForVariable (Set.toList availableElementVariables)
        sortToGenerators = groupBySort generators
    traverse Gen.element sortToGenerators
  where
    generatorForVariable :: ElementVariable Variable -> TermGenerator
    generatorForVariable variable =
        TermGenerator
            { arity = 0
            , sort = SpecificSort (extractSort variable)
            , generator = variableGenerator variable
            }

    variableGenerator variable _termGenerator sort = do
        Monad.when (sort /= extractSort variable) (error "Sort mismatch.")
        return (mkElemVar variable)

    extractSort :: ElementVariable Variable -> Sort
    extractSort (ElementVariable Variable {variableSort}) = variableSort

setVariableGenerators :: Gen (Map.Map SortRequirements TermGenerator)
setVariableGenerators = do
    (_, Context {availableSetVariables}) <- Reader.ask
    let generators = map generatorForVariable (Set.toList availableSetVariables)
        sortToGenerators = groupBySort generators
    traverse Gen.element sortToGenerators
  where
    generatorForVariable :: SetVariable Variable -> TermGenerator
    generatorForVariable variable =
        TermGenerator
            { arity = 0
            , sort = SpecificSort (extractSort variable)
            , generator = variableGenerator variable
            }

    variableGenerator variable _termGenerator sort = do
        Monad.when (sort /= extractSort variable) (error "Sort mismatch.")
        return (mkSetVar variable)

    extractSort (SetVariable Variable {variableSort}) = variableSort

groupBySort :: [TermGenerator] -> Map.Map SortRequirements [TermGenerator]
groupBySort = groupBy termGeneratorSort

groupBy :: forall a b . Ord b => (a -> b) -> [a] -> Map.Map b [a]
groupBy keyExtractor elements =
    List.foldl' addElement Map.empty elements
  where
    addElement
        :: Map.Map b [a]
        -> a
        -> Map.Map b [a]
    addElement keyToElement element =
        Map.insertWith (++) (keyExtractor element) [element] keyToElement

sortGen :: Gen Sort
sortGen = do
    (Setup { allSorts }, _) <- Reader.ask
    Gen.element allSorts

setVariableGen :: Sort -> Gen (SetVariable Variable)
setVariableGen sort = SetVariable <$> variableGen sort

elementVariableGen :: Sort -> Gen (ElementVariable Variable)
elementVariableGen sort = ElementVariable <$> variableGen sort

variableGen :: Sort -> Gen Variable
variableGen variableSort = do
    variableName <- idGen
    return Variable
        { variableName
        , variableCounter = Nothing
        , variableSort
        }
