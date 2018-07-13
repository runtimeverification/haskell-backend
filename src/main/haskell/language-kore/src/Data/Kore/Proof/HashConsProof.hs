{-|
Module      : Data.Kore.Proof.HashConsProof
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
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
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE NoMonomorphismRestriction #-}



module Data.Kore.Proof.HashConsProof where

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

import           Data.Kore.Proof.Proof
import           Data.Kore.Proof.Dummy


import           GHC.Generics (Generic)
import           Data.Hashable
import           Data.Functor.Compose

type HashConsProof = M.Map Int (PropF Term LargeRule Int) 

data ProofWithHashF p = ProofWithHashF Int (PropF Term LargeRule p)
    deriving(Show, Generic)
type ProofWithHash = Fix ProofWithHashF

instance Hashable ProofWithHash where 
    hashWithSalt s (Fix (ProofWithHashF n p)) = s `hashWithSalt` n `hashWithSalt` p

getHash (Fix (ProofWithHashF h _)) = h

-- p :: PropF Term LargeRule Proof 
-- fmap addHash p :: PropF Term LargeRule ProofWithHash
addHash :: Proof -> ProofWithHash
addHash (Fix p) = Fix $ ProofWithHashF h p'
  where p' = fmap addHash p :: PropF Term LargeRule ProofWithHash
        h = hash p' :: Int 

toHashConsProof
    :: Proof 
    -> HashConsProof
toHashConsProof = undefined

