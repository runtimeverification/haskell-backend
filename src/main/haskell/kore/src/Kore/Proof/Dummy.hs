{-|
Module      : Kore.Proof.Dummy
Description : Dummy instances of stuff for testing.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.IndexedModule.MetadataTools
       ( SortTools )

import Kore.ASTUtils.SmartConstructors

var :: MetaOrObject level => String -> Variable level
var x = x `varS` defaultSort

sym :: MetaOrObject level => String -> SymbolOrAlias level
sym x = x `symS` []

var_ :: MetaOrObject level => String -> String -> Variable level
var_ x s =
  Variable (noLocationId x) (mkSort s)

defaultSort :: MetaOrObject level => Sort level
defaultSort = mkSort "*"



dummyEnvironment
  :: forall r . MetaOrObject Object
  => (Given (SortTools Object) => r)
  -> r
dummyEnvironment = give (dummySortTools @Object)

dummySortTools
    :: MetaOrObject level => SortTools level
dummySortTools = const ApplicationSorts
    { applicationSortsOperands = []
    , applicationSortsResult = defaultSort
    }
