{-|
Module      : Data.Kore.Proof.Dummy
Description : Dummy instances of stuff for testing. 
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Data.Kore.Proof.Dummy where


import           Data.Maybe
import           Data.Reflection
import           Data.Fix
import           Data.Foldable
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import           Data.Fix
import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.IndexedModule.MetadataTools


import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.ASTUtils.Substitution

pattern V x = Var_ x

var :: MetaOrObject level => String -> Variable level
var x = 
  Variable (noLocationId x) (testSort "S")  

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
    , getResultSort    = const $ testSort "S"
    }

testSort 
  :: MetaOrObject level 
  => String
  -> Sort level
testSort name =
    SortVariableSort $ SortVariable
        { getSortVariable = noLocationId name }