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

module Data.Kore.Unification.NewProof where

import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix
import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
-- Proof datatype that allows for creating and discharging assumptions
-- Allows for easier, more compact proofs
-- Can be converted to the old type

type Formula level var = Fix (Pattern level var)

data Line ix rule formula
  = Line
  { claim         :: formula
  , justification :: rule ix
  , assumptions   :: S.Set ix
  } deriving (Show)

type Proof ix rule formula = M.Map ix (Line ix rule formula)

discharge 
  :: (Ord ix, MonadState s m)
  => ix 
  -> ix 
  -> Lens' s (Proof ix rule (Formula level var)) 
  -> m ix
discharge ix aix proof = do
  Just line <- M.lookup ix <$> use proof
  Just assumption <- M.lookup ix <$> use proof
  let line' = line 
        { assumptions = S.delete ix (assumptions line) 
        , claim = implies assumption line
        }
  addLine line' proof
  
implies a b = Fix $ ImpliesPattern $ Implies 
  { impliesSort = placeholderSort
  , impliesFirst  = claim a
  , impliesSecond = claim b
  }

placeholderSort =
  SortVariableSort $ SortVariable { getSortVariable = noLocationId "FIXME: The whole AST datatype" }

addLine 
  :: (Ord ix, MonadState s m) 
  => Line ix rule (Formula level var) 
  -> Lens' s (Proof ix rule (Formula level var)) 
  -> m ix
addLine line proof = do
  ix <- getNextIx <$> use proof
  proof %= M.insert ix line
  return ix

assume 
  :: (Ord ix, MonadState s m) 
  => Line ix rule (Formula level var) 
  -> Lens' s (Proof ix rule (Formula level var)) 
  -> m ix
assume line proof = do
  ix <- getNextIx <$> use proof
  proof %= M.insert ix line { assumptions = S.singleton ix }
  return ix 

getNextIx = undefined

collectAssumptions line lines = line 
  { assumptions = S.unions $ fmap assumptions lines
  }

-- class ProofSystem ix var line proof where 
--   discharge :: ix  -> line -> line
--   abstract  :: var -> line -> line

--   addLine   :: line
--             -> proof
--             -> (ix, proof)
--   assume    :: line 
--             -> proof
--             -> (ix, proof)