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

import qualified Data.Set as S
import qualified Data.Map as M

-- data Proof ix rule formula =
--   Proof
--   { index       :: Map ix (Int,formula)
--   , claims      :: Seq (ix,formula)
--   , derivations :: Map ix (rule ix)
--   }
--   deriving (Show)

data Line ix rule formula
  = Line
  { claim         :: formula
  , justification :: rule ix
  , assumptions   :: S.Set ix
  }

type Proof ix rule formula = M.Map ix (Line ix rule formula)

class ProofSystem ix var line proof where 
  discharge :: ix  -> line -> line
  abstract  :: var -> line -> line

  addLine   :: line
            -> proof
            -> (ix, proof)