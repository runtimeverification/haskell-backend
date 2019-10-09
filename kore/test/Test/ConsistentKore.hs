module Test.ConsistentKore
    ( CollectionSorts (..)
    , Context (..)
    , termLikeGen
    ) where

import qualified Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Comonad.Trans.Cofree
    ( CofreeF ((:<))
    )
import Control.Monad.Reader
    ( ReaderT
    )
import qualified Control.Monad.Reader as Reader
import qualified Data.Functor.Foldable as Recursive
import Data.Maybe
    ( catMaybes
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

termLikeGenImpl
    :: Range.Size
    -> Sort
    -> Gen (TermLike Variable)
termLikeGenImpl (Range.Size size) sort
  | size == 0 = do
    generators <- nullaryTermGenerators sort
    TermGenerator {generator} <- Gen.element generators
    generator (error "Unexpected request to create child") sort
  | otherwise = do
    generators <- termGenerators sort
    TermGenerator {generator} <- Gen.element generators
    generator (termLikeGenImpl (Range.Size $ size - 1)) sort
  where
    nullaryTermGenerators :: Sort -> Gen [TermGenerator]
    nullaryTermGenerators nullarySort =
        filter isNullary <$> termGenerators nullarySort

    isNullary :: TermGenerator -> Bool
    isNullary TermGenerator {arity} = arity == 0

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

termGenerators :: Sort -> Gen [TermGenerator]
termGenerators sort = do
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
            , evaluatedGenerator sort
            ]
        )
    literals <- (keepJusts . sequence)
        [ maybeStringLiteralGenerator sort ]
    dv <- (keepJusts . sequence)
        [ maybeIntDVGenerator sort
        , maybeBoolDVGenerator sort
        , maybeStringDVGenerator sort
        ]
    variable <- keepJusts (allVariableGenerators sort)
    symbol <- symbolGenerators sort
    alias <- aliasGenerators sort
    allBuiltin <- allBuiltinGenerators sort
    return
        (  generators
        ++ literals
        ++ dv
        ++ variable
        ++ symbol
        ++ alias
        ++ allBuiltin
        )

data TermGenerator = TermGenerator
    { arity :: !Integer
    , generator
        :: (Sort -> Gen (TermLike Variable))
        -> Sort
        -> Gen (TermLike Variable)
    }

data BuiltinGenerator = BuiltinGenerator
    { arity :: !Integer
    , generator
        :: (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    }

withContext :: Monad m => r -> ReaderT r m a -> ReaderT r m a
withContext r = Reader.local (const r)

nullaryOperatorGenerator
    :: TermLike Variable
    -> Gen TermGenerator
nullaryOperatorGenerator builder =
    return TermGenerator
        { arity = 0
        , generator = const (const (return builder))
        }

nullaryFreeSortOperatorGenerator
    :: (Sort -> TermLike Variable)
    -> Gen TermGenerator
nullaryFreeSortOperatorGenerator builder =
    return TermGenerator
        { arity = 0
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

evaluatedGenerator :: Sort -> Gen TermGenerator
evaluatedGenerator _sort = unaryOperatorGenerator mkEvaluated

maybeStringLiteralGenerator :: Sort -> Gen (Maybe TermGenerator)
maybeStringLiteralGenerator sort = do
    Context {maybeStringLiteralSort} <- Reader.ask
    case maybeStringLiteralSort of
        Nothing -> return Nothing
        Just stringSort
            | sort == stringSort -> do
                str <- stringGen
                generator <- nullaryOperatorGenerator (mkStringLiteral str)
                return (Just generator)
            | otherwise ->
                return Nothing

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

allBuiltinGenerators :: Sort -> Gen [TermGenerator]
allBuiltinGenerators sort = do
    maybeBuiltinGenerators <- sequence
        [ maybeBoolBuiltinGenerator sort
        , maybeIntBuiltinGenerator sort
        , maybeListBuiltinGenerator sort
        , maybeMapBuiltinGenerator sort
        , maybeSetBuiltinGenerator sort
        , maybeStringBuiltinGenerator sort
        ]
    return (map toTermGenerator $ catMaybes maybeBuiltinGenerators)
  where
    toTermGenerator :: BuiltinGenerator -> TermGenerator
    toTermGenerator
        BuiltinGenerator {arity, generator}
      = do
        TermGenerator
            { arity
            , generator =
                \childGenerator _sort -> do
                    builtin <- generator childGenerator
                    return (mkBuiltin builtin)
            }

maybeStringBuiltinGenerator
    :: Sort
    -> Gen (Maybe BuiltinGenerator)
maybeStringBuiltinGenerator sort = do
    Context { maybeStringBuiltinSort } <- Reader.ask
    case maybeStringBuiltinSort of
        Nothing -> return Nothing
        Just stringSort
            | sort == stringSort ->
                return $ Just
                    BuiltinGenerator
                        { arity = 0
                        , generator = stringGenerator stringSort
                        }
            | otherwise -> return Nothing
  where
    stringGenerator
        :: Sort
        -> (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    stringGenerator stringSort _childGenerator = do
        value <- stringGen
        return (BuiltinString.asBuiltin stringSort value)

maybeBoolBuiltinGenerator
    :: Sort
    -> Gen (Maybe BuiltinGenerator)
maybeBoolBuiltinGenerator sort = do
    Context { maybeBoolSort } <- Reader.ask
    case maybeBoolSort of
        Nothing -> return Nothing
        Just boolSort
            | sort == boolSort ->
                return $ Just
                    BuiltinGenerator
                        { arity = 0
                        , generator = boolGenerator boolSort
                        }
            | otherwise -> return Nothing
  where
    boolGenerator
        :: Sort
        -> (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    boolGenerator boolSort _childGenerator = do
        value <- Gen.bool
        return (BuiltinBool.asBuiltin boolSort value)

maybeIntBuiltinGenerator
    :: Sort
    -> Gen (Maybe BuiltinGenerator)
maybeIntBuiltinGenerator sort = do
    Context { maybeIntSort } <- Reader.ask
    case maybeIntSort of
        Nothing -> return Nothing
        Just intSort
            | sort == intSort ->
                return $ Just
                    BuiltinGenerator
                        { arity = 0
                        , generator = intGenerator intSort
                        }
            | otherwise -> return Nothing
  where
    intGenerator
        :: Sort
        -> (Sort -> Gen (TermLike Variable))
        -> Gen (Domain.Builtin (TermLike Concrete) (TermLike Variable))
    intGenerator intSort _childGenerator = do
        value <-
            Gen.integral (Range.constant 0 2000)
        return (BuiltinInt.asBuiltin intSort value)

maybeListBuiltinGenerator
    :: Sort
    -> Gen (Maybe BuiltinGenerator)
maybeListBuiltinGenerator sort = do
    Context { maybeListSorts } <- Reader.ask
    case maybeListSorts of
        Nothing -> return Nothing
        Just CollectionSorts {collectionSort, elementSort}
            | collectionSort == sort ->
                return $ Just
                    BuiltinGenerator
                        { arity = 5
                        , generator = listGenerator collectionSort elementSort
                        }
            | otherwise -> return Nothing
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


maybeMapBuiltinGenerator
    :: Sort
    -> Gen (Maybe BuiltinGenerator)
maybeMapBuiltinGenerator sort = do
    Context { maybeMapSorts } <- Reader.ask
    case maybeMapSorts of
        Nothing -> return Nothing
        Just CollectionSorts {collectionSort}
            | collectionSort == sort -> error "Not implemented yet."
            | otherwise -> return Nothing

maybeSetBuiltinGenerator
    :: Sort
    -> Gen
        (Maybe BuiltinGenerator)
maybeSetBuiltinGenerator sort = do
    Context { maybeSetSorts } <- Reader.ask
    case maybeSetSorts of
        Nothing -> return Nothing
        Just CollectionSorts {collectionSort}
            | collectionSort == sort -> error "Not implemented yet."
            | otherwise -> return Nothing

maybeStringDVGenerator
    :: Sort
    -> Gen (Maybe TermGenerator)
maybeStringDVGenerator sort = do
    Context { maybeStringBuiltinSort } <- Reader.ask
    maybeDVGenerator
        sort
        maybeStringBuiltinSort
        stringGen

stringGen :: Gen Text
stringGen = Gen.text (Range.linear 0 64) (Reader.lift Gen.unicode)

maybeIntDVGenerator
    :: Sort
    -> Gen (Maybe TermGenerator)
maybeIntDVGenerator sort = do
    Context { maybeIntSort } <- Reader.ask
    maybeDVGenerator
        sort
        maybeIntSort
        (Text.pack . show <$> Gen.int (Range.constant 0 2000))

maybeBoolDVGenerator
    :: Sort
    -> Gen (Maybe TermGenerator)
maybeBoolDVGenerator sort = do
    Context { maybeBoolSort } <- Reader.ask
    maybeDVGenerator sort maybeBoolSort (Text.pack . show <$> Gen.bool)

maybeDVGenerator
    :: Sort
    -> Maybe Sort
    -> Gen Text
    -> Gen (Maybe TermGenerator)
maybeDVGenerator sort maybeSort valueGenerator =
    case maybeSort of
        Nothing -> return Nothing
        Just dvSort
            | sort == dvSort ->
                return $ Just
                    TermGenerator
                        { arity = 0
                        , generator = dvGenerator
                        }
            | otherwise -> return Nothing
  where
    dvGenerator _childGenerator domainValueSort = do
        value <- valueGenerator
        return
            (mkDomainValue DomainValue
                { domainValueSort
                , domainValueChild = mkStringLiteral value
                }
            )

symbolGenerators
    :: Sort
    -> Gen [TermGenerator]
symbolGenerators sort = do
    Context {allSymbols} <- Reader.ask
    return $ catMaybes (map (maybeSymbolGenerator sort) allSymbols)

maybeSymbolGenerator :: Sort -> Internal.Symbol -> Maybe TermGenerator
maybeSymbolGenerator
    sort
    symbol@Internal.Symbol
        { symbolParams = []
        , symbolSorts = ApplicationSorts
            { applicationSortsOperands
            , applicationSortsResult
            }
        }
  | applicationSortsResult == sort =
    Just TermGenerator
        { arity = toInteger $ length applicationSortsOperands
        , generator = applicationGenerator
        }
  | otherwise = Nothing
  where
    applicationGenerator termGenerator _sort = do
        terms <- mapM termGenerator applicationSortsOperands
        return (mkApplySymbol symbol terms)
maybeSymbolGenerator
    _
    Internal.Symbol
        { symbolParams = _ : _
        }
  =
    error "Not implemented."

aliasGenerators
    :: Sort
    -> Gen [TermGenerator]
aliasGenerators sort = do
    Context {allAliases} <- Reader.ask
    return $ catMaybes (map (maybeAliasGenerator sort) allAliases)

maybeAliasGenerator
    :: Sort -> Internal.Alias (TermLike Variable) -> Maybe TermGenerator
maybeAliasGenerator
    sort
    alias@Internal.Alias
        { aliasParams = []
        , aliasSorts = ApplicationSorts
            { applicationSortsOperands
            , applicationSortsResult
            }
        }
  | applicationSortsResult == sort =
    Just TermGenerator
        { arity = toInteger $ length applicationSortsOperands
        , generator = applicationGenerator
        }
  | otherwise = Nothing
  where
    applicationGenerator termGenerator _sort = do
        terms <- mapM termGenerator applicationSortsOperands
        return (mkApplyAlias alias terms)
maybeAliasGenerator
    _
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

allVariableGenerators :: Sort -> Gen [Maybe TermGenerator]
allVariableGenerators sort =
    sequence
        [ maybeSetVariableGenerator sort
        , maybeElementVariableGenerator sort
        ]

maybeElementVariableGenerator :: Sort -> Gen (Maybe TermGenerator)
maybeElementVariableGenerator sort = do
    Context {allowedElementVariables} <- Reader.ask
    let variablesForSort =
            filter (variableHasSort sort) (Set.toList allowedElementVariables)
    if null variablesForSort
        then return Nothing
        else return $ Just TermGenerator
            { arity = 0
            , generator = variableGenerator variablesForSort
            }
  where
    variableGenerator allowedVariables _childGenerator _sort =
        mkElemVar <$> Gen.element allowedVariables

    variableHasSort :: Sort -> ElementVariable Variable -> Bool
    variableHasSort requestedSort (ElementVariable Variable {variableSort}) =
        requestedSort == variableSort

maybeSetVariableGenerator :: Sort -> Gen (Maybe TermGenerator)
maybeSetVariableGenerator sort = do
    Context {allowedSetVariables} <- Reader.ask
    let variablesForSort =
            filter (variableHasSort sort) (Set.toList allowedSetVariables)
    if null variablesForSort
        then return Nothing
        else return $ Just TermGenerator
            { arity = 0
            , generator = variableGenerator variablesForSort
            }
  where
    variableGenerator allowedVariables _childGenerator _sort =
        mkSetVar <$> Gen.element allowedVariables

    variableHasSort :: Sort -> SetVariable Variable -> Bool
    variableHasSort requestedSort (SetVariable Variable {variableSort}) =
        requestedSort == variableSort

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
