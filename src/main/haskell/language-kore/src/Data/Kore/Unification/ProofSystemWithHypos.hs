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

module Data.Kore.Unification.NewProof where

import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix
import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore

data ProofLine ix rule formula
  = ProofLine
  { claim         :: formula
  , justification :: rule ix
  , assumptions   :: S.Set ix
  } deriving (Show)

type Proof ix rule formula = M.Map ix (ProofLine ix rule formula)

class (Ord ix, Show ix) => Indexing ix where 
  zeroIx :: ix 
  nextIx :: ix -> ix

class (Functor rule, Traversable rule) => Rules rule where
  assumption :: rule ix
  elim :: ix -> ix -> rule ix

class Formula formula where
  implies :: formula -> formula -> formula

makeRule0 formula rule = do
  addLine ProofLine 
    { claim = formula
    , justification = rule
    , assumptions = S.empty
    }

makeRule1 formula rule ix1 = do
  Just line1 <- M.lookup ix1 <$> get
  addLine ProofLine 
    { claim = formula (claim line1)
    , justification = rule ix
    , assumptions = assumptions line1
    }

makeRule2 formula rule ix1 ix2 = do
  Just line1 <- M.lookup ix1 <$> get
  Just line2 <- M.lookup ix2 <$> get
  addLine ProofLine 
    { claim = formula (claim line1) (claim line2)
    , justification = rule ix1 ix2
    , assumptions = S.unions [assumptions line1, assumptions line2]
    }

makeRule3 formula rule ix1 ix2 ix3 = do
  Just line1 <- M.lookup ix1 <$> get
  Just line2 <- M.lookup ix2 <$> get
  Just line3 <- M.lookup ix3 <$> get
  addLine ProofLine 
    { claim = formula (claim line1) (claim line2) (claim line3)
    , justification = rule ix1 ix2 ix3
    , assumptions = S.unions [assumptions line1, assumptions line2, assumptions line3]
    }

lookupLine 
  :: Indexing ix 
  => ix 
  -> State (Proof ix rule formula) (ProofLine ix rule formula)
lookupLine ix = do
  line' <- M.lookup ix <$> get
  case line' of
    Just line -> return line
    Nothing -> error $
      "Proof line at " 
      ++ show ix 
      ++ " not found."
      -- This shouldn't ever be a user error, I think. 
class 
  ( Indexing ix
  , Rules rule
  , Formula formula) 
  => ProofSystem ix rule formula where 

  getNextIx :: State (Proof ix rule formula) ix
  getNextIx = do 
    maxIx <- M.lookupMax <$> get
    return $ case maxIx of 
      Just (ix,_) -> nextIx ix 
      Nothing     -> zeroIx

  assume :: formula -> State (Proof ix rule formula) ix
  assume formula = do
    ix <- getNextIx
    let line = ProofLine
          { claim = formula
          , justification = assumption
          , assumptions = S.singleton ix
          }
    modify $ M.insert ix line
    return ix

  discharge :: ix -> ix -> State (Proof ix rule formula) ix
  discharge ix1 ix2 = do
    Just hypothesis <- M.lookup ix1 <$> get
    Just conclusion <- M.lookup ix2 <$> get
    let line = ProofLine
          { claim = implies (claim hypothesis) (claim conclusion)
          , justification = elim ix1 ix2
          , assumptions = S.delete ix1 $ assumptions conclusion
          }
    addLine line

  addLine :: ProofLine ix rule formula -> State (Proof ix rule formula) ix
  addLine line = do
    ix <- getNextIx
    modify $ M.insert ix line
    return ix

  

  -- Can also deal with quantifiers:
  
  -- forall :: var -> formula -> var
  -- abs :: var -> ix -> rule ix

  -- abstract :: var -> ix -> State (Proof ix rule formula) ix

  -- etc



