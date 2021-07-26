module Test.Kore.Rewrite.SMT.Representation.Builders (
    emptyDeclarations,
    unresolvedConstructorArg,
    unresolvedConstructorSymbolMap,
    unresolvedDataMap,
    unresolvedIndirectSortMap,
    unresolvedSmthookSymbolMap,
    unresolvedSmtlibSymbolMap,
    unresolvedSort,
    unresolvedSortConstructor,
    unresolvedSortMap,
) where

import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import qualified Kore.Rewrite.SMT.AST as AST (
    Declarations (Declarations),
    Encodable (AlreadyEncoded),
    IndirectSymbolDeclaration (IndirectSymbolDeclaration),
    KoreSortDeclaration (..),
    KoreSymbolDeclaration (..),
    Sort (Sort),
    SortReference (SortReference),
    Symbol (Symbol),
    SymbolReference (SymbolReference),
    UnresolvedConstructor,
    UnresolvedConstructorArgument,
    UnresolvedSort,
    UnresolvedSymbol,
    encodable,
    encode,
 )
import qualified Kore.Rewrite.SMT.AST as AST.DoNotUse
import qualified Kore.Sort as Kore (
    Sort,
 )
import qualified Kore.Syntax.Id as Kore (
    Id,
 )
import Prelude.Kore
import qualified SMT.AST as AST (
    Constructor (Constructor),
    ConstructorArgument (ConstructorArgument),
    DataTypeDeclaration (DataTypeDeclaration),
    FunctionDeclaration (FunctionDeclaration),
    SExpr (Atom),
    SortDeclaration (SortDeclaration),
 )
import qualified SMT.AST as AST.DoNotUse
import Test.Kore (
    testId,
 )
import Test.Kore.Rewrite.SMT.Builders ()

emptyDeclarations :: AST.Declarations sort symbol name
emptyDeclarations = AST.Declarations{sorts = Map.empty, symbols = Map.empty}

unresolvedSortMap :: Kore.Id -> (Kore.Id, AST.UnresolvedSort)
unresolvedSortMap identifier = (identifier, unresolvedSort identifier)

unresolvedSort :: Kore.Id -> AST.UnresolvedSort
unresolvedSort identifier =
    AST.Sort
        { smtFromSortArgs = const $ const $ Just $ AST.encode encodable
        , declaration =
            AST.SortDeclarationSort
                AST.SortDeclaration
                    { name = encodable
                    , arity = 0
                    }
        }
  where
    encodable = AST.encodable identifier

unresolvedDataMap :: Kore.Id -> (Kore.Id, AST.UnresolvedSort)
unresolvedDataMap identifier = (identifier, unresolvedData identifier)

unresolvedData :: Kore.Id -> AST.UnresolvedSort
unresolvedData identifier =
    AST.Sort
        { smtFromSortArgs = const $ const $ Just $ AST.encode encodable
        , declaration =
            AST.SortDeclarationDataType
                AST.DataTypeDeclaration
                    { name = encodable
                    , typeArguments = []
                    , constructors = []
                    }
        }
  where
    encodable = AST.encodable identifier

unresolvedSortConstructor :: Kore.Id -> AST.UnresolvedConstructor
unresolvedSortConstructor identifier =
    AST.Constructor
        { name = AST.SymbolReference identifier
        , arguments = []
        }

unresolvedConstructorArg ::
    Text -> Kore.Sort -> AST.UnresolvedConstructorArgument
unresolvedConstructorArg name sort =
    AST.ConstructorArgument
        { name = AST.encodable (testId name)
        , argType = AST.SortReference sort
        }

unresolvedIndirectSortMap ::
    Kore.Id -> AST.Encodable -> (Kore.Id, AST.UnresolvedSort)
unresolvedIndirectSortMap identifier name =
    (identifier, unresolvedIndirectSort name)

unresolvedIndirectSort :: AST.Encodable -> AST.UnresolvedSort
unresolvedIndirectSort name =
    AST.Sort
        { smtFromSortArgs = const $ const $ Just $ AST.encode name
        , declaration = AST.SortDeclaredIndirectly name
        }

unresolvedConstructorSymbolMap ::
    Kore.Id ->
    Kore.Sort ->
    [Kore.Sort] ->
    (Kore.Id, AST.UnresolvedSymbol)
unresolvedConstructorSymbolMap identifier resultSort argumentSorts =
    ( identifier
    , unresolvedConstructorSymbol identifier resultSort argumentSorts
    )

unresolvedConstructorSymbol ::
    Kore.Id -> Kore.Sort -> [Kore.Sort] -> AST.UnresolvedSymbol
unresolvedConstructorSymbol identifier resultSort argumentSorts =
    AST.Symbol
        { smtFromSortArgs = const $ const $ Just $ AST.encode encodable
        , declaration =
            AST.SymbolConstructor
                AST.IndirectSymbolDeclaration
                    { name = encodable
                    , sortDependencies =
                        AST.SortReference <$> resultSort : argumentSorts
                    }
        }
  where
    encodable = AST.encodable identifier

unresolvedSmtlibSymbolMap ::
    Kore.Id ->
    Text ->
    [Kore.Sort] ->
    Kore.Sort ->
    (Kore.Id, AST.UnresolvedSymbol)
unresolvedSmtlibSymbolMap identifier encodedName inputSorts resultSort =
    (identifier, unresolvedSmtlibSymbol encodedName inputSorts resultSort)

unresolvedSmtlibSymbol ::
    Text ->
    [Kore.Sort] ->
    Kore.Sort ->
    AST.UnresolvedSymbol
unresolvedSmtlibSymbol encodedName inputSorts resultSort =
    AST.Symbol
        { smtFromSortArgs =
            const $
                const $
                    Just $
                        AST.Atom encodedName
        , declaration =
            AST.SymbolDeclaredDirectly
                AST.FunctionDeclaration
                    { name = AST.AlreadyEncoded (AST.Atom encodedName)
                    , inputSorts = map AST.SortReference inputSorts
                    , resultSort = AST.SortReference resultSort
                    }
        }

unresolvedSmthookSymbolMap ::
    Kore.Id ->
    Text ->
    [Kore.Sort] ->
    (Kore.Id, AST.UnresolvedSymbol)
unresolvedSmthookSymbolMap identifier encodedName sortDependencies =
    (identifier, unresolvedSmthookSymbol encodedName sortDependencies)

unresolvedSmthookSymbol ::
    Text -> [Kore.Sort] -> AST.UnresolvedSymbol
unresolvedSmthookSymbol encodedName sortDependencies =
    AST.Symbol
        { smtFromSortArgs =
            const $
                const $
                    Just $
                        AST.Atom encodedName
        , declaration =
            AST.SymbolBuiltin
                AST.IndirectSymbolDeclaration
                    { name = AST.AlreadyEncoded (AST.Atom encodedName)
                    , sortDependencies = fmap AST.SortReference sortDependencies
                    }
        }
