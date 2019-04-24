{-|
Module      : Kore.Step.SMT.AST
Description : Data types involved in declaring and using SMT symbols.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.AST
    ( Declarations (..)
    , Encodable (AlreadyEncoded)
    , KoreSortDeclaration (..)
    , KoreSymbolDeclaration (..)
    , SmtDeclarations
    , SmtKoreSymbolDeclaration
    , SmtSort
    , SmtSymbol
    , Sort (..)
    , SortReference (..)
    , Symbol (..)
    , SymbolReference (..)
    , UnresolvedConstructor
    , UnresolvedConstructorArgument
    , UnresolvedDataTypeDeclaration
    , UnresolvedDeclarations
    , UnresolvedFunctionDeclaration
    , UnresolvedKoreSortDeclaration
    , UnresolvedKoreSymbolDeclaration
    , UnresolvedSort
    , UnresolvedSortDeclaration
    , UnresolvedSymbol
    , appendToEncoding
    , encodable
    , encode
    , mergePreferFirst
    ) where

import qualified Data.Map.Merge.Strict as Map.Merge
import           Data.Map.Strict
                 ( Map )
import           Data.Text
                 ( Text )

import qualified Kore.AST.Identifier as Kore
                 ( Id (Id, getId) )
import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Sort as Kore
                 ( Sort )
import           Kore.Step.SMT.Encoder
                 ( encodeName )
import qualified SMT.AST as AST

data Sort sort symbol name =
    Sort
        { smtFromSortArgs
            :: !(  Map (Kore.Id Object) SmtSort
                -> [Kore.Sort Object]
                -> Maybe AST.SExpr
                )
        , declaration :: !(KoreSortDeclaration sort symbol name)
        }

instance (Show sort, Show symbol, Show name)
    => Show (Sort sort symbol name)
  where
    show s@(Sort _ _) =
        case s of
            Sort { smtFromSortArgs = _, declaration } ->
                   "Sort { smtFromSortArgs, declaration = "
                ++ show declaration
                ++ "}"

data Symbol sort name =
    Symbol
        { smtFromSortArgs
            :: !(  Map (Kore.Id Object) SmtSort
                -> [Kore.Sort Object]
                -> Maybe AST.SExpr
                )
        , declaration :: !(KoreSymbolDeclaration sort name)
        }

instance (Show sort, Show name) => Show (Symbol sort name) where
    show s@(Symbol _ _) =
        case s of
            Symbol { smtFromSortArgs = _, declaration } ->
                   "Symbol { smtFromSortArgs, declaration = "
                ++ show declaration
                ++ "}"

data KoreSortDeclaration sort symbol name
    = SortDeclarationDataType !(AST.DataTypeDeclaration sort symbol name)
    | SortDeclarationSort !(AST.SortDeclaration name)
    | SortDeclaredIndirectly !name
    deriving (Eq, Ord, Show)

data KoreSymbolDeclaration sort name
    = SymbolDeclaredDirectly !(AST.FunctionDeclaration sort name)
    | SymbolDeclaredIndirectly !name ![sort]
    deriving (Eq, Ord, Show)

data Declarations sort symbol name =
    Declarations
        { sorts :: Map (Kore.Id Object) (Sort sort symbol name)
        , symbols :: Map (Kore.Id Object) (Symbol sort name)
        }
    deriving Show


newtype SortReference = SortReference { getSortReference :: Kore.Sort Object }
    deriving (Eq, Ord, Show)
newtype SymbolReference =
    SymbolReference { getSymbolReference :: Kore.Id Object }
    deriving (Eq, Ord, Show)
data Encodable
    = AlreadyEncoded !Text
    | Encodable !Text
    -- TODO (virgil): maybe use Id in Encodable to make it more obvious what
    -- happens.
    deriving (Eq, Ord, Show)

type SmtDeclarations = Declarations AST.SExpr Text Text
type SmtKoreSymbolDeclaration = KoreSymbolDeclaration AST.SExpr Text
type SmtSort = Sort AST.SExpr Text Text
type SmtSymbol = Symbol AST.SExpr Text

type UnresolvedConstructorArgument =
    AST.ConstructorArgument SortReference Encodable
type UnresolvedConstructor =
    AST.Constructor SortReference SymbolReference Encodable
type UnresolvedDataTypeDeclaration =
    AST.DataTypeDeclaration SortReference SymbolReference Encodable
type UnresolvedDeclarations =
    Declarations SortReference SymbolReference Encodable
type UnresolvedFunctionDeclaration =
    AST.FunctionDeclaration SortReference Encodable
type UnresolvedKoreSortDeclaration =
    KoreSortDeclaration SortReference SymbolReference Encodable
type UnresolvedKoreSymbolDeclaration =
    KoreSymbolDeclaration SortReference Encodable
type UnresolvedSort =
    Sort SortReference SymbolReference Encodable
type UnresolvedSortDeclaration =
    AST.SortDeclaration Encodable
type UnresolvedSymbol =
    Symbol SortReference Encodable

encodable :: Kore.Id Object -> Encodable
encodable Kore.Id {getId} = Encodable getId

encode :: Encodable -> Text
encode (AlreadyEncoded e) = e
encode (Encodable e) = encodeName e

appendToEncoding :: Encodable -> Text -> Encodable
appendToEncoding (AlreadyEncoded e) t = AlreadyEncoded (e <> t)
appendToEncoding (Encodable e) t = Encodable (e <> t)

mergePreferFirst
    :: Declarations sort symbol name
    -> Declarations sort symbol name
    -> Declarations sort symbol name
mergePreferFirst
    Declarations { sorts = sorts1, symbols = symbols1 }
    Declarations { sorts = sorts2, symbols = symbols2 }
  =
    Declarations
        { sorts = sorts1 `leftMerge` sorts2
        , symbols = symbols1 `leftMerge` symbols2
        }
  where
    leftMerge :: Ord k => Map k v -> Map k v -> Map k v
    leftMerge =
        Map.Merge.merge
            Map.Merge.preserveMissing
            Map.Merge.preserveMissing
            (Map.Merge.zipWithMatched (\ _key left _right -> left))
