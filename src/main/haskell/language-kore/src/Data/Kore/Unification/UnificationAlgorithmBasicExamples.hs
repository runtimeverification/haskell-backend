{-|
Module      : Data.Kore.Unification.UnifierImpl
Description : Datastructures and functionality for performing unification on
              Pure patterns
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
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE StandaloneDeriving     #-}


module Data.Kore.Unification.UnificationAlgorithmBasicExamples where

import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix

import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Monad.Except

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.PureML
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.IndexedModule.MetadataTools

import           Data.Kore.Unification.ProofSystemWithHypos
import           Data.Kore.Unification.UnificationRules
import           Data.Kore.Unification.UnificationAlgorithm
import           Data.Kore.Unification.Error
import           Data.Kore.Unparser.Unparse

import Debug.Trace
import Text.Groom
spy x = trace (groom x) x

a = Fix $ VariablePattern $ Variable (noLocationId "a") placeholderSort 
b = Fix $ VariablePattern $ Variable (noLocationId "b") placeholderSort 
c = Fix $ VariablePattern $ Variable (noLocationId "c") placeholderSort 

app x ys = Fix $ ApplicationPattern $ Application 
  { applicationSymbolOrAlias = x
  , applicationChildren = ys
  }

sym x = SymbolOrAlias 
  { symbolOrAliasConstructor = noLocationId x 
  , symbolOrAliasParams = [] 
  }

aEqb :: Term
aEqb = Fix $ EqualsPattern $ Equals placeholderSort placeholderSort a b 

bEqc :: Term
bEqc = Fix $ EqualsPattern $ Equals placeholderSort placeholderSort b c 

x :: Term 
x = app (sym "C") [a,b,c]

y :: Term 
y = app (sym "C") [a,app (sym "D") [],app (sym "C") [a,a,a]]

example1 
  :: ExceptT (UnificationError Meta) (
     StateT UnificationState (
     Reader (MetadataTools Meta))
     ) ()
example1 = unificationProcedure x y

-- putStrLn $ run example1
run = 
  groom .
  flip runReader dummyMetaTools .
  flip execStateT emptyUnificationState .
  runExceptT
  

emptyProof :: Proof Int UnificationRules Term 
emptyProof = M.empty

emptyUnificationState = 
  UnificationState
  { _activeSet   = S.empty
  , _finishedSet = S.empty
  , _proof       = emptyProof
  }

dummyMetaTools = MetadataTools
    { isConstructor    = const True 
    , isFunctional     = const True 
    , getArgumentSorts = const [] 
    , getResultSort    = const placeholderSort
    }










