{- |
Module      : Kore.Rewrite.SMT.Representation.Resolve
Description : Resolves kore IDs and builds SMT declarations.
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Representation.All (
    build,
) where

import Data.Map.Strict qualified as Map
import Kore.Attribute.Sort.Constructors qualified as Attribute (
    Constructors,
 )
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Rewrite.SMT.AST qualified as AST
import Kore.Rewrite.SMT.Representation.Resolve (
    resolve,
 )
import Kore.Rewrite.SMT.Representation.Sorts qualified as Sorts (
    buildRepresentations,
 )
import Kore.Rewrite.SMT.Representation.Symbols qualified as Symbols (
    buildRepresentations,
 )
import Kore.Syntax.Id (
    Id,
 )
import Prelude.Kore ()

{- | Builds a consistent representation of the sorts and symbols in the given
module and its submodules.

It may ignore sorts and symbols that it can't handle yet (e.g. parameterized
sorts).
-}
build ::
    VerifiedModule Attribute.Symbol ->
    Map.Map Id Attribute.Constructors ->
    AST.SmtDeclarations
build indexedModule sortConstructors =
    resolve (sorts `AST.mergePreferFirst` symbols)
  where
    sorts = Sorts.buildRepresentations indexedModule sortConstructors
    symbols = Symbols.buildRepresentations indexedModule
