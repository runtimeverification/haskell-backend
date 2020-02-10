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

import Control.Monad
    ( join
    )
import qualified Data.Map.Strict as Map
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

import Debug.Trace

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
    removeDuplicates $ resolve (sorts `Step.AST.mergePreferFirst` symbols)
  where
    sorts = Sorts.buildRepresentations indexedModule sortConstructors
    symbols = Symbols.buildRepresentations indexedModule

removeDuplicates :: Step.AST.SmtDeclarations -> Step.AST.SmtDeclarations
removeDuplicates Step.AST.Declarations { sorts, symbols } =
    let x = join $ mapMaybe g (Map.elems sorts)
     in Step.AST.Declarations
         { sorts
         , symbols = filter (f x) symbols
         }
  where
    g :: Step.AST.Sort SMT.AST.SExpr Text Text -> Maybe [Text]
    g Step.AST.Sort { declaration } =
        case declaration of
            Step.AST.SortDeclarationDataType
                ( SMT.AST.DataTypeDeclaration { constructors }
                ) ->
                    Just $ fmap getName constructors
            _ -> Nothing
    f xs Step.AST.Symbol { declaration } =
        case declaration of
            Step.AST.SymbolDeclaredDirectly
                ( SMT.AST.FunctionDeclaration { name }
                ) ->
                    name `notElem` xs
            _ -> True
    getName :: SMT.AST.Constructor sort symbol name -> symbol
    getName = SMT.AST.name


