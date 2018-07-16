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

{-# LANGUAGE AllowAmbiguousTypes       #-}
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



module Data.Kore.Proof.HashConsProof where

import           Control.Monad.State
import           Control.Arrow
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

import           Data.Kore.Proof.Dummy
import           Data.Kore.Proof.Proof
import           Data.Coerce

import           Data.Functor.Compose
import           Data.Hashable
import           GHC.Generics                          (Generic)

type HashConsProof = M.Map Int (PropF Term LargeRule Int)

type HashConsing = State HashConsProof

-- DUMB! That's still quadratic!

-- data ProofWithHashF p = ProofWithHashF Int (PropF Term LargeRule p)
--     deriving(Show, Generic)
-- type ProofWithHash = Fix ProofWithHashF

-- instance Hashable ProofWithHash where
--     hashWithSalt s (Fix (ProofWithHashF n p)) = s `hashWithSalt` n `hashWithSalt` p

-- getHash (Fix (ProofWithHashF h _)) = h

-- -- p :: PropF Term LargeRule Proof
-- -- fmap addHash p :: PropF Term LargeRule ProofWithHash
-- addHash :: Proof -> ProofWithHash
-- addHash (Fix p) = Fix $ ProofWithHashF h p'
--   where p' = fmap addHash p :: PropF Term LargeRule ProofWithHash
--         h = hash p' :: Int


-- I am not happy with approach.
-- Was hoping for more principled alg
-- That actually defines a Hashable instance. 

-- initHashProof = put (M.empty)

-- pseudoHash 
--     :: Proof 
--     -> Int
-- pseudoHash (Fix proof) = case toList $ justification proof of 
--     [] -> hash proof 
--     _ -> hash $ proof { justification = fmap pseudoHash $ justification proof }

toHashConsProof pf = runState (toHashConsProof' pf) M.empty

toHashConsProof'
    :: Proof
    -> HashConsing Int
toHashConsProof' (Fix proof) = do
    j' <- mapM toHashConsProof' $ justification proof 
    let proof' = proof { justification = j' }
    let h = hash proof'
    modify (M.insert h proof')
    return h

g' pf = runState (go pf) (M.empty, M.empty, 0)

go 
    :: Proof 
    -> State (M.Map Int Int, HashConsProof, Int) Int 
go (Fix proof) = do 
    j' <- mapM go $ justification proof 
    let proof' = proof { justification = j' }
    (hashTable, orderedTable, next) <- get :: State (M.Map Int Int, HashConsProof, Int) (M.Map Int Int, HashConsProof, Int) 
    let h = hash proof' 
    let (hashTable', orderedTable', this, next') = 
          case M.lookup h hashTable of 
            Nothing -> (M.insert h next hashTable, M.insert next proof' orderedTable, next, next+1)
            Just m -> (hashTable, orderedTable, m, next)
    put (hashTable', orderedTable', next')
    return this



