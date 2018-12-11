{-|
Module      : Kore.Proof.Dummy
Description : Dummy instances of stuff for testing.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}

module Kore.Proof.Dummy where

import Data.Reflection
import Data.Text
       ( Text )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.ASTUtils.SmartConstructors
import Kore.IndexedModule.MetadataTools
       ( SymbolOrAliasSorts )
import Kore.Sort

var :: MetaOrObject level => Text -> Variable level
var x = x `varS` defaultSort

sym :: MetaOrObject level => Text -> SymbolOrAlias level
sym x = x `symS` []

var_ :: MetaOrObject level => Text -> Text -> Variable level
var_ x s =
  Variable (noLocationId x) (mkSort s)

defaultSort :: MetaOrObject level => Sort level
defaultSort = mkSort "*"



dummyEnvironment
  :: forall r . (Given (SymbolOrAliasSorts Object) => r)
  -> r
dummyEnvironment = give (dummySymbolOrAliasSorts @Object)

dummySymbolOrAliasSorts
    :: MetaOrObject level => SymbolOrAliasSorts level
dummySymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = []
    , applicationSortsResult = defaultSort
    }
