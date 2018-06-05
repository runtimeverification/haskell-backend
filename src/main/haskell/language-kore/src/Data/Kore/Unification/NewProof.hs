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
import           Control.Lens
import           Control.Monad.State
-- Proof datatype that allows for creating and discharging assumptions
-- Allows for easier, more compact proofs
-- Can be converted to the old type

data Line ix rule formula
  = Line
  { claim         :: formula
  , justification :: rule ix
  , assumptions   :: S.Set ix
  } deriving (Show)

type Proof ix rule formula = M.Map ix (Line ix rule formula)

discharge ix aix proof = do
  Just line <- M.lookup ix <$> use proof
  Just assumption <- M.lookup aix <$> use proof
  let line' = line 
        { assumptions = S.delete ix (assumptions line) 
        , claim = implies assumption line
        }
  addLine line' proof
  
implies = undefined

addLine line proof = do
  ix <- getNextIx <$> use proof
  proof %= M.insert ix line
  return ix

assume :: (Ord ix, MonadState s m) => Line ix rule formula -> Lens' s (Proof ix rule formula) -> m ix
assume line proof = do
  ix <- getNextIx <$> use proof
  let line' = line { assumptions = S.singleton ix }
  proof %= M.insert ix line'
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