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
import           Data.Kore.Unparser.Unparse

import           Data.Kore.Unparser.Unparse

import Debug.Trace
import Text.Groom
spy x = trace (groom x) x

var x = 
  Fix $ VariablePattern $ Variable (noLocationId x) placeholderSort 

app x ys = Fix $ ApplicationPattern $ Application 
  { applicationSymbolOrAlias = x
  , applicationChildren = ys
  }

sym x = SymbolOrAlias 
  { symbolOrAliasConstructor = noLocationId x 
  , symbolOrAliasParams = [] 
  }

t1 :: Term 
t1 =
  app (sym "C") 
  [ var "a"
  , var "b"
  , var "c"
  ]

t2 :: Term 
t2 = 
  app (sym "C") 
  [ var "a"
  , app (sym "D") []
  , app (sym "C") 
    [ var "a"
    , var "a"
    , var "a"]
  ]

t3 :: Term
t3 = app (sym "F") []

t4 :: Term 
t4 = undefined

example1 
  :: ReaderT (MetadataTools Meta) (
     StateT UnificationState (
     ExceptT (UnificationError) 
     Identity))
    ()
example1 = unificationProcedure t1 t2

example2 
  :: ReaderT (MetadataTools Meta) (
     StateT UnificationState (
     ExceptT (UnificationError) 
     Identity))
    ()
example2 = unificationProcedure t2 t3

-- AWFUL HACK! I just wanted legible output as fast as possible
-- Pretty print properly soon.
-- putStrLn $ run example1
run = 
  unescapeLol . 
  groomString .
  -- (\(UnificationState activeSet finishedSet proof) -> 
  --   (finishedSet, (fmap.fmap) UnparseWrapper proof)
  -- ) . 
  (\x -> case x of 
    Right (UnificationState activeSet finishedSet proof) -> 
      show (finishedSet, (fmap.fmap) (("\n" ++) . unparseToString) proof)
    Left err -> show (err :: UnificationError)
  ) . 
  runExcept .
  flip execStateT emptyUnificationState .
  flip runReaderT dummyMetaTools 
  

unescapeLol [] = []
unescapeLol s = 
  case (reads s, break (=='"') s) of 
    ([(here, later)], _) -> here ++ unescapeLol later
    (_, (earlier, here)) -> earlier ++ unescapeLol here  

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










