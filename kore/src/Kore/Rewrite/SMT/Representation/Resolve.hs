{- |
Module      : Kore.Rewrite.SMT.Representation.Resolve
Description : Resolves kore IDs and builds SMT declarations.
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Representation.Resolve (
    resolve,
) where

import Control.Error.Safe (
    assertMay,
 )
import Data.Map.Strict qualified as Map
import Data.Text (
    Text,
 )
import Kore.Debug
import Kore.Rewrite.SMT.AST (
    Declarations (Declarations),
    Encodable,
    IndirectSymbolDeclaration (IndirectSymbolDeclaration),
    KoreSortDeclaration (SortDeclarationDataType, SortDeclarationSort, SortDeclaredIndirectly),
    KoreSymbolDeclaration (SymbolBuiltin, SymbolConstructor, SymbolDeclaredDirectly),
    SmtDeclarations,
    Sort (Sort),
    SortReference (SortReference),
    Symbol (Symbol),
    SymbolReference (SymbolReference),
    UnresolvedConstructor,
    UnresolvedConstructorArgument,
    UnresolvedDataTypeDeclaration,
    UnresolvedDeclarations,
    UnresolvedFunctionDeclaration,
    UnresolvedIndirectSymbolDeclaration,
    UnresolvedKoreSortDeclaration,
    UnresolvedKoreSymbolDeclaration,
    UnresolvedSort,
    UnresolvedSortDeclaration,
    UnresolvedSymbol,
    encode,
 )
import Kore.Rewrite.SMT.AST qualified as DoNotUse
import Kore.Sort qualified as Kore (
    Sort (SortActualSort),
    SortActual (SortActual),
 )
import Kore.Sort qualified as SortActual (
    SortActual (..),
 )
import Kore.Syntax.Id qualified as Kore (
    Id,
 )
import Prelude.Kore
import SMT qualified

data Resolvers sort symbol name = Resolvers
    { sortResolver :: SortReference -> Maybe sort
    , symbolResolver :: SymbolReference -> Maybe symbol
    , nameResolver :: Encodable -> name
    , sortDeclaresSymbol :: SortReference -> Kore.Id -> Bool
    }

{- | Enforces consistency on the given declarations (i.e. all referenced sorts
and symbols must be declared). Removes all declarations with missing references.
-}
resolve :: UnresolvedDeclarations -> SmtDeclarations
resolve declarations =
    resolveDeclarations (smtResolvers checkedDeclarations) checkedDeclarations
  where
    checkedDeclarations = removeBrokenReferences declarations

smtResolvers ::
    UnresolvedDeclarations ->
    Resolvers SMT.SExpr Text SMT.SExpr
smtResolvers Declarations{sorts, symbols} =
    Resolvers
        { sortResolver = referenceCheckSort
        , symbolResolver = referenceCheckSymbol
        , nameResolver = encode
        , sortDeclaresSymbol = sortDeclaresSymbolImpl sorts
        }
  where
    referenceCheckSort
        ( SortReference
                ( Kore.SortActualSort
                        Kore.SortActual
                            { sortActualName
                            , sortActualSorts = []
                            }
                    )
            ) =
            case Map.lookup sortActualName sorts of
                Nothing ->
                    (error . unlines)
                        [ "All references should be resolved before transforming"
                        , "to smt declarations."
                        ]
                Just Sort{sortSmtFromSortArgs} ->
                    case sortSmtFromSortArgs Map.empty [] of
                        Nothing ->
                            (error . unlines)
                                [ "Expecting to be able to produce sort representation"
                                , "for defining it."
                                ]
                        Just value -> return value
    referenceCheckSort _ =
        error "Unimplemented: sort with arguments."

    referenceCheckSymbol SymbolReference{getSymbolReference} =
        case Map.lookup getSymbolReference symbols of
            Nothing ->
                (error . unlines)
                    [ "All references should be resolved before transforming"
                    , "to smt declarations."
                    ]
            Just Symbol{symbolSmtFromSortArgs} ->
                case symbolSmtFromSortArgs Map.empty [] of
                    Nothing ->
                        (error . unlines)
                            [ "Expecting to be able to produce symbol"
                            , "representation for defining it."
                            ]
                    Just (SMT.Atom name) -> return name
                    Just _ ->
                        error
                            "Unable to understand symbol representation."

removeBrokenReferences :: UnresolvedDeclarations -> UnresolvedDeclarations
removeBrokenReferences declarations@Declarations{sorts, symbols} =
    if not (shouldContinue afterOneStep)
        then afterOneStep
        else removeBrokenReferences afterOneStep
  where
    afterOneStep :: UnresolvedDeclarations
    afterOneStep =
        resolveDeclarations (referenceCheckResolvers declarations) declarations

    shouldContinue :: UnresolvedDeclarations -> Bool
    shouldContinue Declarations{sorts = newSorts, symbols = newSymbols} =
        case (sortComparison, symbolComparison) of
            (LT, _) -> error "Unexpected increase in sort count"
            (_, LT) -> error "Unexpected increase in symbol count"
            (EQ, EQ) -> False
            (_, _) -> True
      where
        sortComparison = compare (Map.size sorts) (Map.size newSorts)
        symbolComparison = compare (Map.size symbols) (Map.size newSymbols)

referenceCheckResolvers ::
    UnresolvedDeclarations ->
    Resolvers SortReference SymbolReference Encodable
referenceCheckResolvers Declarations{sorts, symbols} =
    Resolvers
        { sortResolver = referenceCheckSort
        , symbolResolver = referenceCheckSymbol
        , nameResolver = id
        , sortDeclaresSymbol = sortDeclaresSymbolImpl sorts
        }
  where
    referenceCheckSort
        reference@( SortReference
                        ( Kore.SortActualSort
                                Kore.SortActual
                                    { sortActualName
                                    , sortActualSorts = []
                                    }
                            )
                    ) =
            traceMaybe D_SMT_referenceCheckSort [debugArg "reference" reference] $
                do
                    _ <- Map.lookup sortActualName sorts
                    return reference
    referenceCheckSort reference =
        traceMaybe
            D_SMT_referenceCheckSort
            [debugArg "reference" reference]
            Nothing

    referenceCheckSymbol reference@SymbolReference{getSymbolReference} =
        traceMaybe D_SMT_referenceCheckSymbol [debugArg "reference" reference] $
            do
                _ <- Map.lookup getSymbolReference symbols
                return reference

resolveDeclarations ::
    (Show sort, Show symbol, Show name) =>
    Resolvers sort symbol name ->
    UnresolvedDeclarations ->
    Declarations sort symbol name
resolveDeclarations
    resolvers
    Declarations{sorts, symbols} =
        Declarations
            { sorts = Map.mapMaybe (resolveSort resolvers) sorts
            , symbols = Map.mapMaybeWithKey (resolveSymbol resolvers) symbols
            }

resolveSort ::
    (Show sort, Show symbol, Show name) =>
    Resolvers sort symbol name ->
    UnresolvedSort ->
    Maybe (Sort sort symbol name)
resolveSort
    resolvers
    Sort{sortSmtFromSortArgs, sortDeclaration} =
        traceMaybe D_SMT_resolveSort [debugArg "declaration" sortDeclaration] $
            do
                newDeclaration <- resolveKoreSortDeclaration resolvers sortDeclaration
                return
                    Sort
                        { sortSmtFromSortArgs = sortSmtFromSortArgs
                        , sortDeclaration = newDeclaration
                        }

resolveKoreSortDeclaration ::
    Resolvers sort symbol name ->
    UnresolvedKoreSortDeclaration ->
    Maybe (KoreSortDeclaration sort symbol name)
resolveKoreSortDeclaration resolvers (SortDeclarationDataType declaration) =
    SortDeclarationDataType
        <$> resolveDataTypeDeclaration resolvers declaration
resolveKoreSortDeclaration resolvers (SortDeclarationSort declaration) =
    return
        ( SortDeclarationSort
            (resolveSortDeclaration resolvers declaration)
        )
resolveKoreSortDeclaration
    Resolvers{nameResolver}
    (SortDeclaredIndirectly name) =
        Just (SortDeclaredIndirectly (nameResolver name))

resolveDataTypeDeclaration ::
    Resolvers sort symbol name ->
    UnresolvedDataTypeDeclaration ->
    Maybe (SMT.DataTypeDeclaration sort symbol name)
resolveDataTypeDeclaration
    resolvers@Resolvers{nameResolver}
    SMT.DataTypeDeclaration{name, typeArguments, constructors} =
        do
            newConstructors <- mapM (resolveConstructor resolvers) constructors
            return
                SMT.DataTypeDeclaration
                    { name = nameResolver name
                    , typeArguments = map nameResolver typeArguments
                    , constructors = newConstructors
                    }

resolveConstructor ::
    Resolvers sort symbol name ->
    UnresolvedConstructor ->
    Maybe (SMT.Constructor sort symbol name)
resolveConstructor
    resolvers@Resolvers{symbolResolver}
    SMT.Constructor{name, arguments} =
        do
            newName <- symbolResolver name
            newArguments <- mapM (resolveConstructorArgument resolvers) arguments
            return
                SMT.Constructor
                    { name = newName
                    , arguments = newArguments
                    }

resolveConstructorArgument ::
    Resolvers sort symbol name ->
    UnresolvedConstructorArgument ->
    Maybe (SMT.ConstructorArgument sort name)
resolveConstructorArgument
    Resolvers{sortResolver, nameResolver}
    SMT.ConstructorArgument{name, argType} =
        do
            newArgType <- sortResolver argType
            return
                SMT.ConstructorArgument
                    { name = nameResolver name
                    , argType = newArgType
                    }

resolveSortDeclaration ::
    Resolvers sort symbol name ->
    UnresolvedSortDeclaration ->
    SMT.SortDeclaration name
resolveSortDeclaration
    Resolvers{nameResolver}
    SMT.SortDeclaration{name, arity} =
        SMT.SortDeclaration{name = nameResolver name, arity}

resolveSymbol ::
    (Show sort, Show name) =>
    Resolvers sort symbol name ->
    Kore.Id ->
    UnresolvedSymbol ->
    Maybe (Symbol sort name)
resolveSymbol
    resolvers
    symbolId
    Symbol{symbolSmtFromSortArgs, symbolDeclaration} =
        traceMaybe D_SMT_resolveSymbol [debugArg "declaration" symbolDeclaration] $ do
            newDeclaration <-
                resolveKoreSymbolDeclaration resolvers symbolId symbolDeclaration
            return
                Symbol
                    { symbolSmtFromSortArgs = symbolSmtFromSortArgs
                    , symbolDeclaration = newDeclaration
                    }

resolveKoreSymbolDeclaration ::
    Resolvers sort symbol name ->
    Kore.Id ->
    UnresolvedKoreSymbolDeclaration ->
    Maybe (KoreSymbolDeclaration sort name)
resolveKoreSymbolDeclaration resolvers _ (SymbolDeclaredDirectly declaration) =
    SymbolDeclaredDirectly <$> resolveFunctionDeclaration resolvers declaration
resolveKoreSymbolDeclaration
    resolvers
    _
    (SymbolBuiltin indirectDeclaration) =
        SymbolBuiltin
            <$> resolveIndirectBuiltinSymbolDeclaration
                resolvers
                indirectDeclaration
resolveKoreSymbolDeclaration
    resolvers@Resolvers{sortDeclaresSymbol}
    symbolId
    ( SymbolConstructor
            indirectDeclaration@IndirectSymbolDeclaration
                { sortDependencies
                }
        ) =
        do
            -- If the sort does not declare the constructor symbol, and we would try to
            -- use it, we would get a "not declared error" from the SMT. Also,
            -- if it's not declared by the sort, then we don't have
            -- any constraints on it, so there's currently no point in declaring
            -- it separately.
            --
            -- Note that direct smtlib declarations take precedence over constructors,
            -- so we would not reach this line if this symbol had a smtlib attribute.
            assertMay $
                any (flip sortDeclaresSymbol symbolId) sortDependencies

            SymbolConstructor
                <$> resolveIndirectConstructorSymbolDeclaration
                    resolvers
                    indirectDeclaration

resolveIndirectBuiltinSymbolDeclaration ::
    Resolvers sort symbol name ->
    UnresolvedIndirectSymbolDeclaration ->
    Maybe (IndirectSymbolDeclaration sort name)
resolveIndirectBuiltinSymbolDeclaration
    Resolvers{nameResolver}
    IndirectSymbolDeclaration
        { name
        } =
        return
            IndirectSymbolDeclaration
                { name = nameResolver name
                , sortDependencies = []
                }

resolveIndirectConstructorSymbolDeclaration ::
    Resolvers sort symbol name ->
    UnresolvedIndirectSymbolDeclaration ->
    Maybe (IndirectSymbolDeclaration sort name)
resolveIndirectConstructorSymbolDeclaration
    Resolvers{nameResolver, sortResolver}
    IndirectSymbolDeclaration
        { name
        , sortDependencies
        } =
        do
            newSortDependencies <- mapM sortResolver sortDependencies
            return
                IndirectSymbolDeclaration
                    { name = nameResolver name
                    , sortDependencies = newSortDependencies
                    }

resolveFunctionDeclaration ::
    Resolvers sort symbol name ->
    UnresolvedFunctionDeclaration ->
    Maybe (SMT.FunctionDeclaration sort name)
resolveFunctionDeclaration
    Resolvers{sortResolver, nameResolver}
    SMT.FunctionDeclaration{name, inputSorts, resultSort} =
        do
            newInputSorts <- mapM sortResolver inputSorts
            newResultSort <- sortResolver resultSort
            return
                SMT.FunctionDeclaration
                    { name = nameResolver name
                    , inputSorts = newInputSorts
                    , resultSort = newResultSort
                    }

sortDeclaresSymbolImpl ::
    Map.Map Kore.Id UnresolvedSort ->
    SortReference ->
    Kore.Id ->
    Bool
sortDeclaresSymbolImpl
    sorts
    ( SortReference
            ( Kore.SortActualSort
                    Kore.SortActual
                        { sortActualName
                        , sortActualSorts = []
                        }
                )
        )
    symbolId =
        case Map.lookup sortActualName sorts of
            Nothing -> False
            Just Sort{sortDeclaration = SortDeclarationSort _} -> False
            Just Sort{sortDeclaration = SortDeclaredIndirectly _} -> False
            Just Sort{sortDeclaration = SortDeclarationDataType dataType} ->
                dataTypeDeclaresSymbol dataType symbolId
sortDeclaresSymbolImpl _ _ _ = False

dataTypeDeclaresSymbol :: UnresolvedDataTypeDeclaration -> Kore.Id -> Bool
dataTypeDeclaresSymbol
    SMT.DataTypeDeclaration{constructors}
    symbolId =
        any isSameSymbol constructors
      where
        isSameSymbol :: UnresolvedConstructor -> Bool
        isSameSymbol
            SMT.Constructor{name = SymbolReference symbolReferenceId} =
                symbolReferenceId == symbolId
