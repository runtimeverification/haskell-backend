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

module Data.Kore.Unification.NewProof where

import qualified Data.Set as S
import qualified Data.Map as M

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

discharge ix aix proof = 
  let Just line = M.lookup ix proof
      Just assumption = M.lookup aix proof
      line' = line 
        { assumptions = S.delete ix (assumptions line) 
        , claim = implies assumption line
        }
  in addLine line' proof
  
implies = undefined

addLine line proof = 
  let ix = getNextIx proof
  in (ix, M.insert ix line proof)

assume line proof = 
  let ix = getNextIx proof
      line' = line { assumptions = S.singleton ix }
  in (ix, M.insert ix line' proof)

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