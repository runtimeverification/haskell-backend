{-|
Module      : Kore.Step.SMT.Representation.Resolve
Description : Resolves kore IDs and builds SMT declarations.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Representation.All
    ( build
    ) where

import Prelude.Kore

import Data.List
    ( foldl'
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )

import qualified Kore.Attribute.Sort.Constructors as Attribute
    ( Constructors
    )
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.Step.SMT.AST as Step.AST
import Kore.Step.SMT.Representation.Resolve
    ( resolve
    )
import qualified Kore.Step.SMT.Representation.Sorts as Sorts
    ( buildRepresentations
    )
import qualified Kore.Step.SMT.Representation.Symbols as Symbols
    ( buildRepresentations
    )
import Kore.Syntax.Id
    ( Id
    )
import qualified SMT.AST

{-| Builds a consistent representation of the sorts and symbols in the given
module and its submodules.

It may ignore sorts and symbols that it can't handle yet (e.g. parameterized
sorts).
-}
build
    :: VerifiedModule Attribute.Symbol
    -> Map.Map Id Attribute.Constructors
    -> Step.AST.SmtDeclarations
build indexedModule sortConstructors =
    removeDuplicateConstructorDeclarations
    $ resolve (sorts `Step.AST.mergePreferFirst` symbols)
  where
    sorts = Sorts.buildRepresentations indexedModule sortConstructors
    symbols = Symbols.buildRepresentations indexedModule

removeDuplicateConstructorDeclarations
    :: Step.AST.SmtDeclarations
    -> Step.AST.SmtDeclarations
removeDuplicateConstructorDeclarations
    Step.AST.Declarations { sorts, symbols }
  =
    let constructorSymbols =
            foldl' getConstructorNames Set.empty (Map.elems sorts)
     in Step.AST.Declarations
         { sorts
         , symbols = filter (isNotDuplicate constructorSymbols) symbols
         }
  where
    getConstructorNames
        :: Set Text
        -> Step.AST.Sort SMT.AST.SExpr Text Text
        -> Set Text
    getConstructorNames names Step.AST.Sort { declaration } =
        case declaration of
            Step.AST.SortDeclarationDataType
                SMT.AST.DataTypeDeclaration { constructors } ->
                    names <> Set.fromList (getName <$> constructors)
            _ -> names
    isNotDuplicate
        :: Set Text
        -> Step.AST.Symbol SMT.AST.SExpr Text
        -> Bool
    isNotDuplicate constructorSymbols Step.AST.Symbol { declaration } =
        case declaration of
            Step.AST.SymbolDeclaredDirectly
                SMT.AST.FunctionDeclaration { name } ->
                    name `notElem` constructorSymbols
            _ -> True
    getName :: SMT.AST.Constructor sort symbol name -> symbol
    getName = SMT.AST.name
