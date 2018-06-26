{-|
Module      : Data.Kore.Unification.UnificationAlgorithm
Description : Computes MGU from t1 /\ t2, with a proof of correctness
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
{-# LANGUAGE BangPatterns           #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}


module Data.Kore.Unification.UnificationAlgorithm where

import           Data.Fix
import qualified Data.Set as S

import           Control.Lens
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Monad.Except

import           Data.Kore.AST.Common                     ( Pattern(..)
                                                          , Application(..)
                                                          , SymbolOrAlias(..)
                                                          )

import           Data.Kore.AST.MetaOrObject               ( MetaOrObject
                                                          )
import           Data.Kore.IndexedModule.MetadataTools    ( MetadataTools(..)
                                                          ) 

import           Data.Kore.Proof.ProofSystemWithHypos     ( Proof
                                                          , claim 
                                                          , lookupLine
                                                          , assume
                                                          , discharge
                                                          , (%%%=)
                                                          )
import           Data.Kore.Unification.UnificationRules   ( UnificationRules(..)
                                                          , Term
                                                          , Idx
                                                          , makeConjunction
                                                          , splitConjunction
                                                          , pattern Equation
                                                          , lhsIsVariable
                                                          , flipEqn
                                                          , applyRefl
                                                          , applySymmetry
                                                          , applyNoConfusion                                                       , placeholderSort
                                                          , applyIffIntro
                                                          , applyLocalSubstitution
                                                          )


{- 
NOTE:
1) Carrying around ix=Int and constantly dereferencing
is too cumbersome. Instead: carry around the proof lines,
and just hashcons when constructing new Rule ix?
2) Handling multiple states with lenses is not pretty,
but with a few combinators it becomes fairly unobtrusive
and I don't see many better options. 
-}

-- FIXME: Functionality check
-- FIXME: Prop 5.24.3 wrapper

data UnificationState level
  = UnificationState 
  { _activeSet :: ![Idx]
  , _finishedSet :: ![Idx]
  , _proof :: !(Proof Int (UnificationRules level) (Term level))
  } 
  deriving(Show)

data UnificationError level
    = ConstructorClash     (Term level) (Term level)
    | NonConstructorHead   (Term level)
    | NonFunctionalPattern (Term level)
    | OccursCheck          (Term level) (Term level)
  deriving (Eq, Show)

makeLenses ''UnificationState

type UnificationContext level m = 
  ( MonadState (UnificationState level) m
  , MonadReader (MetadataTools level) m
  , MonadError (UnificationError level) m
  ) 

type Unification level a = 
  ReaderT (MetadataTools level) (
  StateT (UnificationState level) (
  ExceptT (UnificationError level) 
  Identity))
  a

-- unificationProcedure x y >>= getSubstList
getSubstList 
  :: MetaOrObject level 
  => Idx 
  -> Unification level [(Term level, Term level)]
getSubstList ix = do 
  ixs <- S.toList <$> proof %%%= splitConjunction ix 
  eqns <- forM ixs $ \ix' -> do 
    (Equation _ _ a b) <- claim <$> proof %%%= lookupLine ix 
    return (a,b)
  return eqns

unificationProcedure 
  :: MetaOrObject level
  => Term level
  -> Term level
  -> Unification level Idx
unificationProcedure a b = do
  (ixMGU, forwardsDirection) <- proveForwardsDirection a b
  backwardsDirection <-
    (claim <$> proof %%%= lookupLine ixMGU)
    >>= proveBackwardsDirection a b
  proof %%%= applyIffIntro forwardsDirection backwardsDirection

proveForwardsDirection
  :: MetaOrObject level
  => Term level
  -> Term level 
  -> Unification level (Idx, Idx)
proveForwardsDirection a b = do 
  tools <- ask
  ixAB <- proof %%%= assume (Equation placeholderSort placeholderSort a b)
  activeSet %= (ixAB :)
  mainLoop
  eqns <- use finishedSet
  ixMGU <- proof %%%= makeConjunction tools eqns
  forwardsDirection <- proof %%%= discharge ixAB ixMGU
  return (ixMGU, forwardsDirection)

proveBackwardsDirection
  :: MetaOrObject level
  => Term level
  -> Term level
  -> Term level 
  -> Unification level Idx 
proveBackwardsDirection a b mgu = do 
  tools <- ask
  ixMGU <- proof %%%= assume mgu
  ixAA  <- proof %%%= applyRefl tools a
  ixBB  <- proof %%%= applyRefl tools b
  mgus <- S.toList <$> proof %%%= splitConjunction ixMGU
  ixAB <- go ixAA ixBB mgus
  proof %%%= discharge ixMGU ixAB
    where go ix1 ix2 [] = proof %%%= applyLocalSubstitution ix1 ix2 [0]
          go ix1 ix2 (eqn : eqns) = do
            ix1' <- proof %%%= applyLocalSubstitution eqn ix1 [0]
            ix2' <- proof %%%= applyLocalSubstitution eqn ix2 [0]
            go ix1' ix2' eqns

mainLoop 
  :: MetaOrObject level
  => Unification level ()
mainLoop = do
  eqns <- use activeSet
  case eqns of
    [] -> return () -- we are done
    (ix : rest) -> do
      activeSet .= rest
      process ix
      mainLoop

process
  :: MetaOrObject level
  => Idx 
  -> Unification level ()
process ix = do
  eqn@(Equation s1 s2 a b) <- claim <$> (proof %%%= lookupLine ix)
  if a == b
  then do return ()
  else if lhsIsVariable eqn
  then do
    if occursInTerm a b
    then do throwError $ OccursCheck a b
    else do
      substituteEverythingInSet ix activeSet
      substituteEverythingInSet ix finishedSet
      finishedSet %= (ix :)
  else if lhsIsVariable (flipEqn eqn)
  then do
    ix' <- proof %%%= applySymmetry ix
    activeSet %= (ix' :)
  else do 
    tools <- ask
    goSplitConstructor tools ix eqn

checkIfOccursInSets 
  :: (MetaOrObject level
  ,  UnificationContext level m)
  => Term level 
  -> m Bool
checkIfOccursInSets !pat = liftM2 (||)
  (occursInSet pat activeSet)
  (occursInSet pat finishedSet)

occursInSet
  :: (MetaOrObject level
  ,  UnificationContext level m)
  => Term level 
  -> Lens' (UnificationState level) [Int]
  -> m Bool
occursInSet !pat !set = do
  ixs <- use set 
  eqns <- mapM (\ix -> claim <$> proof %%%= lookupLine ix) ixs
  return $ any (occursInTerm pat) eqns 

occursInTerm 
  :: MetaOrObject level 
  => Term level 
  -> Term level 
  -> Bool 
occursInTerm !pat !bigPat =
  if pat == bigPat 
    then True
    else foldr (||) False $ fmap (occursInTerm pat) $ unFix bigPat

substituteEverythingInSet
  :: (MetaOrObject level
  ,  UnificationContext level m)
  => Int 
  -> Lens' (UnificationState level) [Int]
  -> m ()
substituteEverythingInSet !ix !set = do
  rest <- use set
  rest' <- (forM rest $ \ix' -> proof %%%= applyLocalSubstitution ix ix' [])
  set .= rest' 
  -- pretty unhappy with lens combinators here. 
  -- am i missing something? 
  -- googled it. seems not. 
  -- TODO: elim no-op proof steps?
      

goSplitConstructor 
  :: (MetaOrObject level
  ,  UnificationContext level m)
  => MetadataTools level
  -> Idx
  -> Term level
  -> m ()
goSplitConstructor !tools !ix !e@(Equation s1 s2 a b)
  | not (isConstructor tools $ getHead a)
      = throwError $ NonConstructorHead a
  | not (isConstructor tools $ getHead a)
      = throwError $ NonConstructorHead b
  | getHead a /= getHead b
      = throwError $ ConstructorClash a b 
  | otherwise
      = equateChildren ix
goSplitConstructor _ _ _ = error "Input should be Equation"

getHead 
  :: MetaOrObject level
  => Term level
  -> SymbolOrAlias level
getHead (Fix (ApplicationPattern (Application head _))) = head
getHead _ = error "Input should be ApplicationPattern"

equateChildren
  :: (MetaOrObject level
  ,  UnificationContext level m)
  => Idx
  -> m ()
equateChildren !ix = do
  tools <- ask
  ix' <- proof %%%= applyNoConfusion tools ix
  ixs' <- proof %%%= splitConjunction ix'
  activeSet %= (S.toList ixs' ++)










