{-|
Module      : Data.Kore.Proof.Dummy
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

module Data.Kore.Proof.Dummy where


import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Data.Fix
import           Data.Fix
import           Data.Foldable
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.IndexedModule.MetadataTools
import qualified Data.Map.Strict                       as M
import           Data.Maybe
import           Data.Reflection
import qualified Data.Set                              as S


import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.ASTUtils.Substitution

pattern V x = Var_ x

var :: MetaOrObject level => String -> Variable level
var x =
  Variable (noLocationId x) (testSort "*")

sym :: MetaOrObject level => String -> SymbolOrAlias level
sym x =
  SymbolOrAlias (noLocationId x) []

var_ :: MetaOrObject level => String -> String -> Variable level
var_ x s =
  Variable (noLocationId x) (testSort s)

varS :: MetaOrObject level => String -> Sort level -> Variable level
varS x s =
  Variable (noLocationId x) s

dummyEnvironment
  :: forall r . MetaOrObject Object
  => (Given (MetadataTools Object) => r)
  -> r
dummyEnvironment = give (dummyMetadataTools @Object)

dummyMetadataTools
  :: MetaOrObject level
  => MetadataTools level
dummyMetadataTools = MetadataTools
    { isConstructor    = const True
    , isFunctional     = const True
    , isFunction       = const True
    , getArgumentSorts = const []
    , getResultSort    = const $ testSort "*"
    }

testSort
  :: MetaOrObject level
  => String
  -> Sort level
testSort name =
    SortVariableSort $ SortVariable
        { getSortVariable = noLocationId name }
