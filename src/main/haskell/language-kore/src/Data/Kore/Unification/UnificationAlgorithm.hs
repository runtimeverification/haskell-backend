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


module Data.Kore.Unification.UnificationAlgorithm where

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
import           Data.Kore.Unification.Error
import           Data.Kore.Unparser.Unparse


{- 
NOTE:
1) Carrying around ix=Int and constantly dereferencing
is too cumbersome. Instead: carry around the proof lines,
and just hashcons when constructing new Rule ix?
2) Handling multiple states with lenses is not pretty,
but with a few combinators it becomes fairly unobtrusive
and I don't see many better options. 
-}

data UnificationState
  = UnificationState 
  { _activeSet :: S.Set Int
  , _finishedSet :: S.Set Int
  , _proof :: Proof Int UnificationRules Term
  } 
  deriving(Show)
  

makeLenses ''UnificationState

type UnificationContext m = 
  ( MonadState UnificationState m
  , MonadReader (MetadataTools Meta) m
  , MonadError (UnificationError Meta) m
  ) 

unificationProcedure 
  :: UnificationContext m 
  => Term 
  -> Term 
  -> m ()
unificationProcedure a b = do
  ixAB <- proof %%%= assume (Equation placeholderSort placeholderSort a b)
  let q = Fix $ VariablePattern $ Variable (noLocationId "q") placeholderSort
  ixqA <- proof %%%= assume (Equation placeholderSort placeholderSort q a)
  activeSet %= S.insert ixAB 
  finishedSet %= S.insert ixqA
  loop 

loop 
  :: UnificationContext m
  => m ()
loop = do
  eqns <- use activeSet
  case S.maxView eqns of 
    Nothing -> return () -- we are done
    Just (ix, rest) -> do
      activeSet .= rest
      process ix
      loop

process
  :: (UnificationContext m)
  => Int 
  -> m ()
process ix = do
  eqn <- claim <$> (proof %%%= lookupLine ix)
  if isTrivial eqn
  then do 
    activeSet %= S.delete ix
  else if lhsIsVariable eqn
  then do
    if occursInTerm (getLHS eqn) (getRHS eqn)
    then do throwError $ undefined -- circularity error
    else do
      occursInSets <- checkIfOccursInSets $ getLHS eqn
      if occursInSets
      then do
        substituteEverythingInSet ix activeSet
        substituteEverythingInSet ix finishedSet
      else do 
        activeSet %= S.delete ix 
        finishedSet %= S.insert ix
  else if lhsIsVariable (flipEqn eqn)
  then do
    activeSet %= S.delete ix
    ix' <- proof %%%= applySymmetry ix
    activeSet %= S.insert ix
  else do 
    tools <- ask
    goSplitConstructor tools ix eqn


checkIfOccursInSets 
  :: (UnificationContext m)
  => Term 
  -> m Bool
checkIfOccursInSets pat = liftM2 (||)
  (occursInSet pat activeSet)
  (occursInSet pat finishedSet)

occursInSet
  :: UnificationContext m 
  => Term 
  -> Lens' UnificationState (S.Set Int)
  -> m Bool
occursInSet pat set = do
  ixs <- S.toList <$> use set 
  eqns <- mapM (\ix -> claim <$> proof %%%= lookupLine ix) ixs
  return $ any (occursInTerm pat) eqns --FIXME: Should really just hashcons

occursInTerm pat bigPat =
  if pat == bigPat 
    then True
    else foldr (||) False $ fmap (occursInTerm pat) $ unFix bigPat

substituteEverythingInSet
  :: UnificationContext m 
  => Int 
  -> Lens' UnificationState (S.Set Int) 
  -> m ()
substituteEverythingInSet ix set = do
  rest <- use set
  forM_ rest $ \ix' -> do
      set %= S.delete ix 
      ix'' <- proof %%%= applySubstitution ix ix' 
      set %= S.insert ix''

goSplitConstructor 
  :: UnificationContext m
  => MetadataTools Meta
  -> Int
  -> Term
  -> m ()
goSplitConstructor tools ix e@(Equation s1 s2 a b)
  | not (isConstructor tools headA)
      = throwError $ NonConstructorHead headA
  | not (isConstructor tools headB)
      = throwError $ NonConstructorHead headB
  | headA /= headB
      = throwError $ ConstructorClash headA headB
  | otherwise
      = equateChildren ix
    where 
      ApplicationPattern (Application headA _) = unFix a
      ApplicationPattern (Application headB _) = unFix a

equateChildren
  :: UnificationContext m
  => Int
  -> m ()
equateChildren ix = do
  ix' <- proof %%%= applyNoConfusion ix
  ixs' <- splitConjunction ix'
  activeSet %= S.union ixs'

-- applyNoConfusion = undefined
splitConjunction ix = do
  eqn <- claim <$> proof %%%= lookupLine ix
  if isConjunction eqn
  then do
    ixLeft  <- proof %%%= applyAndL ix
    ixRight <- proof %%%= applyAndR ix
    splitResultLeft  <- splitConjunction ixLeft 
    splitResultRight <- splitConjunction ixRight 
    return $ S.union splitResultLeft splitResultLeft
  else return S.empty

occursInItself :: Term -> Bool
occursInItself = const False
  
bar 
  :: ExceptT (UnificationError Meta) (
     StateT UnificationState (
     Reader (MetadataTools Meta))
     ) ()
bar = unificationProcedure ca cb

foo :: UnificationState
foo = 
  flip runReader metaTools $
  flip execStateT emptyUnificationState $ 
  runExceptT $
  bar

emptyProof :: Proof Int UnificationRules Term 
emptyProof = M.empty

emptyUnificationState = 
  UnificationState
  { _activeSet   = S.empty
  , _finishedSet = S.empty
  , _proof       = emptyProof
  }

metaTools = MetadataTools
    { isConstructor    = const True
    , isFunctional     = const True
    , getArgumentSorts = const []
    , getResultSort    = const placeholderSort
    }










