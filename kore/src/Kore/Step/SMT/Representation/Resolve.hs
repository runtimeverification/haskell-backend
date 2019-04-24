{-|
Module      : Kore.Step.SMT.Representation.Resolve
Description : Resolves kore IDs and builds SMT declarations.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Representation.Resolve
    ( resolve
    ) where

import qualified Data.Map as Map
import           Data.Text
                 ( Text )

import qualified Kore.Sort as Kore
                 ( Sort (SortActualSort), SortActual (SortActual) )
import qualified Kore.Sort as SortActual
                 ( SortActual (..) )
import           Kore.Step.SMT.AST
                 ( Declarations (Declarations), Encodable,
                 KoreSortDeclaration (SortDeclarationDataType, SortDeclarationSort, SortDeclaredIndirectly),
                 KoreSymbolDeclaration (SymbolDeclaredDirectly, SymbolDeclaredIndirectly),
                 SmtDeclarations, Sort (Sort), SortReference (SortReference),
                 Symbol (Symbol), SymbolReference (SymbolReference),
                 UnresolvedConstructor, UnresolvedConstructorArgument,
                 UnresolvedDataTypeDeclaration, UnresolvedDeclarations,
                 UnresolvedFunctionDeclaration, UnresolvedKoreSortDeclaration,
                 UnresolvedKoreSymbolDeclaration, UnresolvedSort,
                 UnresolvedSortDeclaration, UnresolvedSymbol, encode )
import qualified Kore.Step.SMT.AST as DoNotUse
import qualified SMT

import Kore.Debug

data Resolvers sort symbol name = Resolvers
    { sortResolver :: SortReference -> Maybe sort
    , symbolResolver :: SymbolReference -> Maybe symbol
    , nameResolver :: Encodable -> name
    }

{-| Enforces consistency on the given declarations (i.e. all referenced sorts
and symbols must be declared). Removes all declarations with missing references.
-}
resolve :: UnresolvedDeclarations -> SmtDeclarations
resolve declarations =
    resolveDeclarations (smtResolvers checkedDeclarations) checkedDeclarations
  where
    checkedDeclarations = removeBrokenReferences declarations

smtResolvers
    :: UnresolvedDeclarations
    -> Resolvers SMT.SExpr Text Text
smtResolvers Declarations {sorts, symbols} =
    Resolvers
        { sortResolver = referenceCheckSort
        , symbolResolver = referenceCheckSymbol
        , nameResolver = encode
        }
  where
    referenceCheckSort
        (SortReference
            (Kore.SortActualSort Kore.SortActual
                { sortActualName
                , sortActualSorts = []
                }
            )
        )
      = case Map.lookup sortActualName sorts of
        Nothing -> (error . unlines)
            [ "All references should be resolved before transforming"
            , "to smt declarations."
            ]
        Just Sort { smtFromSortArgs } ->
            case smtFromSortArgs Map.empty [] of
                Nothing -> (error . unlines)
                    [ "Expecting to be able to produce sort representation"
                    , "for defining it."
                    ]
                Just value -> return value
    referenceCheckSort _ =
        error "Unimplemented: sort with arguments."

    referenceCheckSymbol SymbolReference {getSymbolReference} =
        case Map.lookup getSymbolReference symbols of
            Nothing -> (error . unlines)
                [ "All references should be resolved before transforming"
                , "to smt declarations."
                ]
            Just Symbol { smtFromSortArgs } ->
                case smtFromSortArgs Map.empty [] of
                    Nothing -> (error . unlines)
                        [ "Expecting to be able to produce symbol"
                        , "representation for defining it."
                        ]
                    Just (SMT.Atom name) -> return name
                    Just _ -> error
                        "Unable to understand symbol representation."

removeBrokenReferences :: UnresolvedDeclarations -> UnresolvedDeclarations
removeBrokenReferences declarations@Declarations { sorts, symbols } =
    if not (shouldContinue afterOneStep)
    then afterOneStep
    else removeBrokenReferences afterOneStep
  where
    afterOneStep :: UnresolvedDeclarations
    afterOneStep =
        resolveDeclarations (referenceCheckResolvers declarations) declarations

    shouldContinue :: UnresolvedDeclarations -> Bool
    shouldContinue Declarations { sorts = newSorts, symbols = newSymbols } =
        case (sortComparison, symbolComparison) of
            (LT, _) -> error "Unexpected increase in sort count"
            (_, LT) -> error "Unexpected increase in symbol count"
            (EQ, EQ) -> False
            (_, _) -> True
      where
        sortComparison = compare (Map.size sorts) (Map.size newSorts)
        symbolComparison = compare (Map.size symbols) (Map.size newSymbols)

referenceCheckResolvers
    :: UnresolvedDeclarations
    -> Resolvers SortReference SymbolReference Encodable
referenceCheckResolvers Declarations {sorts, symbols} =
    Resolvers
        { sortResolver = referenceCheckSort
        , symbolResolver = referenceCheckSymbol
        , nameResolver = id
        }
  where
    referenceCheckSort
        reference@(SortReference
            (Kore.SortActualSort Kore.SortActual
                { sortActualName
                , sortActualSorts = []
                }
            )
        )
      = traceMaybe D_SMT_referenceCheckSort [debugArg "reference" reference]
        $ do
            _ <- Map.lookup sortActualName sorts
            return reference
    referenceCheckSort reference =
        traceMaybe D_SMT_referenceCheckSort [debugArg "reference" reference]
        $ Nothing

    referenceCheckSymbol reference@SymbolReference {getSymbolReference} =
        traceMaybe D_SMT_referenceCheckSymbol [debugArg "reference" reference]
        $ do
            _ <- Map.lookup getSymbolReference symbols
            return reference

resolveDeclarations
    :: (Show sort, Show symbol, Show name)
    => Resolvers sort symbol name
    -> UnresolvedDeclarations
    -> Declarations sort symbol name
resolveDeclarations
    resolvers
    Declarations { sorts, symbols }
  =
    Declarations
        { sorts = Map.mapMaybe (resolveSort resolvers) sorts
        , symbols = Map.mapMaybe (resolveSymbol resolvers) symbols
        }

resolveSort
    :: (Show sort, Show symbol, Show name)
    => Resolvers sort symbol name
    -> UnresolvedSort
    -> Maybe (Sort sort symbol name)
resolveSort
    resolvers
    Sort { smtFromSortArgs, declaration }
  = traceMaybe D_SMT_resolveSort [debugArg "declaration" declaration]
    $ do
    newDeclaration <- resolveKoreSortDeclaration resolvers declaration
    return Sort
        { smtFromSortArgs = smtFromSortArgs
        , declaration = newDeclaration
        }

resolveKoreSortDeclaration
    :: Resolvers sort symbol name
    -> UnresolvedKoreSortDeclaration
    -> Maybe (KoreSortDeclaration sort symbol name)
resolveKoreSortDeclaration resolvers (SortDeclarationDataType declaration) =
    SortDeclarationDataType
        <$> resolveDataTypeDeclaration resolvers declaration
resolveKoreSortDeclaration resolvers (SortDeclarationSort declaration) =
    return
        (SortDeclarationSort
            (resolveSortDeclaration resolvers declaration)
        )
resolveKoreSortDeclaration
    Resolvers {nameResolver} (SortDeclaredIndirectly name)
  =
    Just (SortDeclaredIndirectly (nameResolver name))

resolveDataTypeDeclaration
    :: Resolvers sort symbol name
    -> UnresolvedDataTypeDeclaration
    -> Maybe (SMT.DataTypeDeclaration sort symbol name)
resolveDataTypeDeclaration
    resolvers@Resolvers { nameResolver }
    SMT.DataTypeDeclaration { name, typeArguments, constructors }
  = do
    newConstructors <- mapM (resolveConstructor resolvers) constructors
    return SMT.DataTypeDeclaration
        { name = nameResolver name
        , typeArguments = map nameResolver typeArguments
        , constructors = newConstructors
        }

resolveConstructor
    :: Resolvers sort symbol name
    -> UnresolvedConstructor
    -> Maybe (SMT.Constructor sort symbol name)
resolveConstructor
    resolvers@Resolvers { symbolResolver }
    SMT.Constructor { name, arguments }
  = do
    newName <- symbolResolver name
    newArguments <- mapM (resolveConstructorArgument resolvers) arguments
    return SMT.Constructor
        { name = newName
        , arguments = newArguments
        }

resolveConstructorArgument
    :: Resolvers sort symbol name
    -> UnresolvedConstructorArgument
    -> Maybe (SMT.ConstructorArgument sort name)
resolveConstructorArgument
    Resolvers { sortResolver, nameResolver }
    SMT.ConstructorArgument { name, argType }
  = do
    newArgType <- sortResolver argType
    return SMT.ConstructorArgument
        { name = nameResolver name
        , argType = newArgType
        }

resolveSortDeclaration
    :: Resolvers sort symbol name
    -> UnresolvedSortDeclaration
    -> SMT.SortDeclaration name
resolveSortDeclaration
    Resolvers { nameResolver }
    SMT.SortDeclaration { name, arity }
  =
    SMT.SortDeclaration { name = nameResolver name, arity }

resolveSymbol
    :: (Show sort, Show name)
    => Resolvers sort symbol name
    -> UnresolvedSymbol
    -> Maybe (Symbol sort name)
resolveSymbol
    resolvers
    Symbol { smtFromSortArgs, declaration }
  = traceMaybe D_SMT_resolveSymbol [debugArg "declaration" declaration] $ do
    newDeclaration <- resolveKoreSymbolDeclaration resolvers declaration
    return Symbol
        { smtFromSortArgs = smtFromSortArgs
        , declaration = newDeclaration
        }

resolveKoreSymbolDeclaration
    :: Resolvers sort symbol name
    -> UnresolvedKoreSymbolDeclaration
    -> Maybe (KoreSymbolDeclaration sort name)
resolveKoreSymbolDeclaration resolvers (SymbolDeclaredDirectly declaration) =
    SymbolDeclaredDirectly <$> resolveFunctionDeclaration resolvers declaration
resolveKoreSymbolDeclaration
    Resolvers {sortResolver, nameResolver}
    (SymbolDeclaredIndirectly name sorts)
  = do
    newSorts <- mapM sortResolver sorts
    return $ SymbolDeclaredIndirectly (nameResolver name) newSorts

resolveFunctionDeclaration
    :: Resolvers sort symbol name
    -> UnresolvedFunctionDeclaration
    -> Maybe (SMT.FunctionDeclaration sort name)
resolveFunctionDeclaration
    Resolvers { sortResolver, nameResolver }
    SMT.FunctionDeclaration { name, inputSorts, resultSort }
  = do
    newInputSorts <- mapM sortResolver inputSorts
    newResultSort <- sortResolver resultSort
    return SMT.FunctionDeclaration
        { name = nameResolver name
        , inputSorts = newInputSorts
        , resultSort = newResultSort
        }
