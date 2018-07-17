{-|
Module      : Data.Kore.Proof.LinedBasedProof
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeSynonymInstances      #-}



module Data.Kore.Proof.LinedBasedProof where

import           Control.Arrow
import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State.Strict

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

import           Data.Kore.Proof.Dummy
import           Data.Kore.Proof.Proof
import           Data.Coerce

import           Data.Functor.Compose
import           Data.Hashable
import           GHC.Generics                          (Generic)

type LineBasedProof = M.Map Int (PropF Term LargeRule Int)

toLineProof :: Proof -> LineBasedProof
toLineProof proof =
    execState (go proof) (M.empty, M.empty, 0) ^. _2
    where 
        go (Fix proof) = do 
            j' <- mapM go $ justification proof
            let proof' = proof { justification = j' }
            (hashTable, orderedTable, next) <- get 
            let h = hash proof'
            (!hashTable, !orderedTable, !next) <- get 
            case M.lookup h hashTable of 
              Just m -> do 
                return m 
              Nothing -> do 
                put ( M.insert h next hashTable
                    , M.insert next proof' orderedTable
                    , next+1)
                return next






