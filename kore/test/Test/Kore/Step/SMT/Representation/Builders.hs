module Test.Kore.Step.SMT.Representation.Builders
    ( emptyDeclarations
    , unresolvedConstructorArg
    , unresolvedConstructorSymbolMap
    , unresolvedDataMap
    , unresolvedIndirectSortMap
    , unresolvedSmthookSymbolMap
    , unresolvedSmtlibSymbolMap
    , unresolvedSort
    , unresolvedSortConstructor
    , unresolvedSortMap
    ) where

import Test.Kore.Step.SMT.Builders ()

import qualified Data.Map as Map
import           Data.Text
                 ( Text )

import qualified Kore.AST.Identifier as Kore
                 ( Id )
import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Sort as Kore
                 ( Sort )
import qualified Kore.Step.SMT.AST as AST
                 ( Declarations (Declarations), Encodable (AlreadyEncoded),
                 IndirectSymbolDeclaration (IndirectSymbolDeclaration),
                 KoreSortDeclaration (..), KoreSymbolDeclaration (..),
                 Sort (Sort), SortReference (SortReference),
                 SortReference (SortReference), Symbol (Symbol),
                 SymbolReference (SymbolReference), UnresolvedConstructor,
                 UnresolvedConstructorArgument, UnresolvedSort,
                 UnresolvedSymbol, encodable, encode )
import qualified Kore.Step.SMT.AST as AST.DoNotUse
import qualified SMT.AST as AST
                 ( Constructor (Constructor),
                 ConstructorArgument (ConstructorArgument),
                 DataTypeDeclaration (DataTypeDeclaration),
                 FunctionDeclaration (FunctionDeclaration), SExpr (Atom),
                 SortDeclaration (SortDeclaration) )
import qualified SMT.AST as AST.DoNotUse

import Test.Kore
       ( testId )

emptyDeclarations :: AST.Declarations sort symbol name
emptyDeclarations = AST.Declarations {sorts = Map.empty, symbols = Map.empty}

unresolvedSortMap :: Kore.Id Object -> (Kore.Id Object, AST.UnresolvedSort)
unresolvedSortMap identifier = (identifier, unresolvedSort identifier)

unresolvedSort :: Kore.Id Object -> AST.UnresolvedSort
unresolvedSort identifier =
    AST.Sort
        { smtFromSortArgs = const $ const $ Just
            $ AST.Atom (AST.encode encodable)
        , declaration = AST.SortDeclarationSort AST.SortDeclaration
            { name = encodable
            , arity = 0
            }
        }
  where
    encodable = AST.encodable identifier

unresolvedDataMap :: Kore.Id Object -> (Kore.Id Object, AST.UnresolvedSort)
unresolvedDataMap identifier = (identifier, unresolvedData identifier)

unresolvedData :: Kore.Id Object -> AST.UnresolvedSort
unresolvedData identifier =
    AST.Sort
        { smtFromSortArgs = const $ const $ Just
            $ AST.Atom (AST.encode encodable)
        , declaration = AST.SortDeclarationDataType AST.DataTypeDeclaration
            { name = encodable
            , typeArguments = []
            , constructors = []
            }
        }
  where
    encodable = AST.encodable identifier

unresolvedSortConstructor :: Kore.Id Object -> AST.UnresolvedConstructor
unresolvedSortConstructor identifier =
    AST.Constructor
        { name = AST.SymbolReference identifier
        , arguments = []
        }

unresolvedConstructorArg
    :: Text -> Kore.Sort Object -> AST.UnresolvedConstructorArgument
unresolvedConstructorArg name sort =
    AST.ConstructorArgument
        { name = AST.encodable (testId name)
        , argType = AST.SortReference sort
        }

unresolvedIndirectSortMap
    :: Kore.Id Object -> AST.Encodable -> (Kore.Id Object, AST.UnresolvedSort)
unresolvedIndirectSortMap identifier name =
    (identifier, unresolvedIndirectSort name)

unresolvedIndirectSort :: AST.Encodable -> AST.UnresolvedSort
unresolvedIndirectSort name =
    AST.Sort
        { smtFromSortArgs = const $ const $ Just
            $ AST.Atom (AST.encode name)
        , declaration = AST.SortDeclaredIndirectly name
        }

unresolvedConstructorSymbolMap
    :: Kore.Id Object
    -> [Kore.Sort Object]
    -> (Kore.Id Object, AST.UnresolvedSymbol)
unresolvedConstructorSymbolMap identifier sorts =
    (identifier, unresolvedConstructorSymbol identifier sorts)

unresolvedConstructorSymbol
    :: Kore.Id Object -> [Kore.Sort Object] -> AST.UnresolvedSymbol
unresolvedConstructorSymbol identifier sorts =
    AST.Symbol
        { smtFromSortArgs = const $ const $ Just
            $ AST.Atom (AST.encode encodable)
        , declaration = AST.SymbolDeclaredIndirectly
            AST.IndirectSymbolDeclaration
                { name = encodable, sorts = map AST.SortReference sorts }
        }
  where
    encodable = AST.encodable identifier

unresolvedSmtlibSymbolMap
    :: Kore.Id Object
    -> Text
    -> [Kore.Sort Object]
    -> Kore.Sort Object
    -> (Kore.Id Object, AST.UnresolvedSymbol)
unresolvedSmtlibSymbolMap identifier encodedName inputSorts resultSort =
    ( identifier, unresolvedSmtlibSymbol encodedName inputSorts resultSort )

unresolvedSmtlibSymbol
    :: Text
    -> [Kore.Sort Object]
    -> Kore.Sort Object
    -> AST.UnresolvedSymbol
unresolvedSmtlibSymbol encodedName inputSorts resultSort =
    AST.Symbol
        { smtFromSortArgs = const $ const $ Just
            $ AST.Atom encodedName
        , declaration = AST.SymbolDeclaredDirectly
            AST.FunctionDeclaration
                { name = AST.AlreadyEncoded encodedName
                , inputSorts = map AST.SortReference inputSorts
                , resultSort = AST.SortReference resultSort
                }
        }

unresolvedSmthookSymbolMap
    :: Kore.Id Object
    -> Text
    -> [Kore.Sort Object]
    -> (Kore.Id Object, AST.UnresolvedSymbol)
unresolvedSmthookSymbolMap identifier encodedName sorts =
    (identifier, unresolvedSmthookSymbol encodedName sorts)

unresolvedSmthookSymbol
    :: Text -> [Kore.Sort Object] -> AST.UnresolvedSymbol
unresolvedSmthookSymbol encodedName sorts =
    AST.Symbol
        { smtFromSortArgs = const $ const $ Just
            $ AST.Atom encodedName
        , declaration = AST.SymbolDeclaredIndirectly
            AST.IndirectSymbolDeclaration
                { name = AST.AlreadyEncoded encodedName
                , sorts = map AST.SortReference sorts
                }
        }
