{-|
Module      : Kore.Step.SMT.Representation.Resolve
Description : Resolves kore IDs and builds SMT declarations.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Step.SMT.Representation.All
  ( build
    )
where

import qualified Kore.Attribute.Axiom as Attribute
  ( Axiom
    )
import qualified Kore.Attribute.Symbol as Attribute
  ( Symbol
    )
import Kore.IndexedModule.IndexedModule
  ( VerifiedModule
    )
import qualified Kore.Step.SMT.AST as AST
import Kore.Step.SMT.Representation.Resolve
  ( resolve
    )
import qualified Kore.Step.SMT.Representation.Sorts as Sorts
  ( buildRepresentations
    )
import qualified Kore.Step.SMT.Representation.Symbols as Symbols
  ( buildRepresentations
    )

{-| Builds a consistent representation of the sorts and symbols in the given
module and its submodules.

It may ignore sorts and symbols that it can't handle yet (e.g. parameterized
sorts).
-}
build
  :: VerifiedModule Attribute.Symbol Attribute.Axiom
  -> AST.SmtDeclarations
build indexedModule =
  resolve (sorts `AST.mergePreferFirst` symbols)
  where
    sorts = Sorts.buildRepresentations indexedModule
    symbols = Symbols.buildRepresentations indexedModule
