module Test.ConsistentKore
    ( CollectionSorts (..)
    , Context (..)
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
    { allSymbols :: ![Internal.Symbol]
    , allAliases :: ![Internal.Alias (TermLike Variable)]
    , allSorts :: ![Sort]
    , allowedElementVariables :: !(Set.Set (ElementVariable Variable))
    , allowedSetVariables :: !(Set.Set (SetVariable Variable))
    , maybeIntSort :: !(Maybe Sort)
    , maybeBoolSort :: !(Maybe Sort)
    , maybeListSorts :: !(Maybe CollectionSorts)
    , maybeMapSorts :: !(Maybe CollectionSorts)
    , maybeSetSorts :: !(Maybe CollectionSorts)
    , maybeStringLiteralSort :: !(Maybe Sort)
    , maybeStringBuiltinSort :: !(Maybe Sort)
    , metadataTools :: SmtMetadataTools Attribute.Symbol
    }

type Gen = ReaderT Context Hedgehog.Gen

runTermGen :: Context -> Gen a -> Hedgehog.Gen a
runTermGen context generator =
    Reader.runReaderT generator context

addQuantifiedSetVariable :: SetVariable Variable -> Context -> Context
addQuantifiedSetVariable
    variable
    context@Context {allowedSetVariables}
  =
    context {allowedSetVariables = Set.insert variable allowedSetVariables}

addQuantifiedElementVariable :: ElementVariable Variable -> Context -> Context
addQuantifiedElementVariable
    variable
    context@Context {allowedElementVariables}
  =
    context
        {allowedElementVariables = Set.insert variable allowedElementVariables}

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
    generators <- sequence
        (   [ andGenerator
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
        )
    literals <- (keepJusts . sequence)
        [ maybeStringLiteralGenerator ]
    dv <- (keepJusts . sequence)
        [ maybeIntDVGenerator
        , maybeBoolDVGenerator
        , maybeStringDVGenerator
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

withContext :: Monad m => r -> ReaderT r m a -> ReaderT r m a
withContext r = Reader.local (const r)

nullaryFreeSortOperatorGenerator
    :: (Sort -> TermLike Variable)
    -> Gen TermGenerator
nullaryFreeSortOperatorGenerator builder =
    return TermGenerator
        { arity = 0
        , sort = AnySort
        , generator = worker
        }
  where
    worker _childGenerator resultSort =
        return (builder resultSort)

unaryOperatorGenerator
    :: (TermLike Variable -> TermLike Variable)
    -> Gen TermGenerator
unaryOperatorGenerator builder = do
    context <- Reader.ask
    return TermGenerator
        { arity = 1
        , sort = AnySort
        , generator = worker context
        }
  where
    worker context childGenerator childSort =
        builder
            <$> withContext context (childGenerator childSort)

unaryFreeSortOperatorGenerator
    :: (Sort -> TermLike Variable -> TermLike Variable)
    -> Gen TermGenerator
unaryFreeSortOperatorGenerator builder = do
    context <- Reader.ask
    return TermGenerator
        { arity = 1
        , sort = AnySort
        , generator = worker context
        }
  where
    worker context childGenerator resultSort = withContext context $ do
        childSort <- sortGen
        child <- childGenerator childSort
        return (builder resultSort child)

unaryQuantifiedElementOperatorGenerator
    :: (ElementVariable Variable -> TermLike Variable -> TermLike Variable)
    -> Gen TermGenerator
unaryQuantifiedElementOperatorGenerator builder = do
    context <- Reader.ask
    variableSort <- sortGen
    quantifiedVariable <- elementVariableGen variableSort
    return TermGenerator
        { arity = 1
        , sort = AnySort
        , generator =
            worker
                quantifiedVariable
                (addQuantifiedElementVariable quantifiedVariable context)
        }
  where
    worker variable context childGenerator childSort =
        withContext context $ builder variable <$> childGenerator childSort

unaryQuantifiedSetOperatorGenerator
    :: (SetVariable Variable -> TermLike Variable -> TermLike Variable)
    -> Gen TermGenerator
unaryQuantifiedSetOperatorGenerator builder = do
    context <- Reader.ask
    variableSort <- sortGen
    quantifiedVariable <- setVariableGen variableSort
    return TermGenerator
        { arity = 1
        , sort = AnySort
        , generator =
            worker
                quantifiedVariable
                (addQuantifiedSetVariable quantifiedVariable context)
        }
  where
    worker variable context childGenerator childSort =
        withContext context $ builder variable <$> childGenerator childSort

binaryFreeSortOperatorGenerator
    :: (Sort -> TermLike Variable -> TermLike Variable -> TermLike Variable)
    -> Gen TermGenerator
binaryFreeSortOperatorGenerator builder = do
    context <- Reader.ask
    return TermGenerator
        { arity = 2
        , sort = AnySort
        , generator = worker context
        }
  where
    worker context childGenerator resultSort = withContext context $ do
        childSort <- sortGen
        child1 <- childGenerator childSort
        child2 <- childGenerator childSort
        return (builder resultSort child1 child2)

binaryOperatorGenerator
    :: (TermLike Variable -> TermLike Variable -> TermLike Variable)
    -> Gen TermGenerator
binaryOperatorGenerator builder = do
    context <- Reader.ask
    return TermGenerator
        { arity = 2
        , sort = AnySort
        , generator = worker context
        }
  where
    worker context childGenerator childSort =
        builder
            <$> withContext context (childGenerator childSort)
            <*> withContext context (childGenerator childSort)

andGenerator :: Gen TermGenerator
andGenerator = binaryOperatorGenerator mkAnd

bottomGenerator :: Gen TermGenerator
bottomGenerator = nullaryFreeSortOperatorGenerator mkBottom

ceilGenerator :: Gen TermGenerator
ceilGenerator = unaryFreeSortOperatorGenerator mkCeil

equalsGenerator :: Gen TermGenerator
equalsGenerator = binaryFreeSortOperatorGenerator mkEquals

existsGenerator :: Gen TermGenerator
existsGenerator = unaryQuantifiedElementOperatorGenerator mkExists

floorGenerator :: Gen TermGenerator
floorGenerator = unaryFreeSortOperatorGenerator mkFloor

forallGenerator :: Gen TermGenerator
forallGenerator = unaryQuantifiedElementOperatorGenerator mkForall

iffGenerator :: Gen TermGenerator
iffGenerator = binaryOperatorGenerator mkIff

impliesGenerator :: Gen TermGenerator
impliesGenerator = binaryOperatorGenerator mkImplies

inGenerator :: Gen TermGenerator
inGenerator = binaryFreeSortOperatorGenerator mkIn

muGenerator :: Gen TermGenerator
muGenerator = unaryQuantifiedSetOperatorGenerator mkMu

notGenerator :: Gen TermGenerator
notGenerator = unaryOperatorGenerator mkNot

nuGenerator :: Gen TermGenerator
nuGenerator = unaryQuantifiedSetOperatorGenerator mkNu

orGenerator :: Gen TermGenerator
orGenerator = binaryOperatorGenerator mkOr

rewritesGenerator :: Gen TermGenerator
rewritesGenerator = binaryOperatorGenerator mkRewrites

topGenerator :: Gen TermGenerator
topGenerator = nullaryFreeSortOperatorGenerator mkTop

evaluatedGenerator :: Gen TermGenerator
evaluatedGenerator = unaryOperatorGenerator mkEvaluated

maybeStringLiteralGenerator :: Gen (Maybe TermGenerator)
maybeStringLiteralGenerator = do
    Context {maybeStringLiteralSort} <- Reader.ask
    case maybeStringLiteralSort of
        Nothing -> return Nothing
        Just stringSort ->
            return $ Just TermGenerator
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
    maybeBuiltinGenerators <- sequence
        [ maybeBoolBuiltinGenerator
        , maybeIntBuiltinGenerator
        , maybeListBuiltinGenerator
        , maybeMapBuiltinGenerator
        , maybeSetBuiltinGenerator
        , maybeStringBuiltinGenerator
        ]
    let termGeneratorList =
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

maybeStringBuiltinGenerator :: Gen (Maybe BuiltinGenerator)
maybeStringBuiltinGenerator = do
    Context { maybeStringBuiltinSort } <- Reader.ask
    case maybeStringBuiltinSort of
        Nothing -> return Nothing
        Just stringSort ->
            return $ Just
                BuiltinGenerator
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

maybeBoolBuiltinGenerator :: Gen (Maybe BuiltinGenerator)
maybeBoolBuiltinGenerator = do
    Context { maybeBoolSort } <- Reader.ask
    case maybeBoolSort of
        Nothing -> return Nothing
        Just boolSort ->
            return $ Just
                BuiltinGenerator
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

maybeIntBuiltinGenerator :: Gen (Maybe BuiltinGenerator)
maybeIntBuiltinGenerator = do
    Context { maybeIntSort } <- Reader.ask
    case maybeIntSort of
        Nothing -> return Nothing
        Just intSort ->
            return $ Just BuiltinGenerator
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

maybeListBuiltinGenerator :: Gen (Maybe BuiltinGenerator)
maybeListBuiltinGenerator = do
    Context { maybeListSorts } <- Reader.ask
    case maybeListSorts of
        Nothing -> return Nothing
        Just CollectionSorts {collectionSort, elementSort} ->
            return $ Just
                BuiltinGenerator
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
        Context {metadataTools} <- Reader.ask
        elements <-
            Gen.seq (Range.constant 0 5)
            (childGenerator listElementSort)
        return (BuiltinList.asBuiltin metadataTools listSort elements)


maybeMapBuiltinGenerator :: Gen (Maybe BuiltinGenerator)
maybeMapBuiltinGenerator = do
    Context { maybeMapSorts } <- Reader.ask
    case maybeMapSorts of
        Nothing -> return Nothing
        Just _ -> error "Not implemented yet."

maybeSetBuiltinGenerator :: Gen (Maybe BuiltinGenerator)
maybeSetBuiltinGenerator = do
    Context { maybeSetSorts } <- Reader.ask
    case maybeSetSorts of
        Nothing -> return Nothing
        Just _ -> error "Not implemented yet."

maybeStringDVGenerator :: Gen (Maybe TermGenerator)
maybeStringDVGenerator = do
    Context { maybeStringBuiltinSort } <- Reader.ask
    return (maybeDVGenerator maybeStringBuiltinSort stringGen)

stringGen :: Gen Text
stringGen = Gen.text (Range.linear 0 64) (Reader.lift Gen.unicode)

maybeIntDVGenerator :: Gen (Maybe TermGenerator)
maybeIntDVGenerator = do
    Context { maybeIntSort } <- Reader.ask
    return
        (maybeDVGenerator
            maybeIntSort
            (Text.pack . show <$> Gen.int (Range.constant 0 2000))
        )

maybeBoolDVGenerator :: Gen (Maybe TermGenerator)
maybeBoolDVGenerator = do
    Context { maybeBoolSort } <- Reader.ask
    return (maybeDVGenerator maybeBoolSort (Text.pack . show <$> Gen.bool))

maybeDVGenerator
    :: Maybe Sort
    -> Gen Text
    -> Maybe (TermGenerator)
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
    Context {allSymbols} <- Reader.ask
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
    Context {allAliases} <- Reader.ask
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
    Context {allowedElementVariables} <- Reader.ask
    let generators =
            map generatorForVariable (Set.toList allowedElementVariables)
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
    Context {allowedSetVariables} <- Reader.ask
    let generators = map generatorForVariable (Set.toList allowedSetVariables)
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
    Context { allSorts } <- Reader.ask
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

keepJusts :: Gen [Maybe a] -> Gen [a]
keepJusts = fmap catMaybes
