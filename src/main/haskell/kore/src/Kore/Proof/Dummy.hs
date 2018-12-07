{-|
Module      : Kore.Proof.Dummy
Description : Dummy instances of stuff for testing.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes #-}

module Kore.Proof.Dummy where

import Data.Reflection
import Data.Text
       ( Text )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.IndexedModule.MetadataTools
       ( SymbolOrAliasSorts )

import Kore.ASTUtils.SmartConstructors

var :: Text -> Variable level
var x = x `varS` defaultSort

sym :: Text -> SymbolOrAlias level
sym x = x `symS` []

var_ :: Text -> Text -> Variable level
var_ x s =
  Variable (noLocationId x) (mkSort s)

defaultSort :: Sort level
defaultSort = mkSort "*"



dummyEnvironment
  :: forall r . (Given (SymbolOrAliasSorts Object) => r)
  -> r
dummyEnvironment = give (dummySymbolOrAliasSorts @Object)

dummySymbolOrAliasSorts :: SymbolOrAliasSorts level
dummySymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = []
    , applicationSortsResult = defaultSort
    }
