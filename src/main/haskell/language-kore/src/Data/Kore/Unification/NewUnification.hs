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
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}

module Data.Kore.Unification.NewUnification where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML
import           Data.Kore.FixTraversals
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.Unification.Error

import           Data.Kore.Unification.NewProof

import           Control.Monad.Except
import           Control.Monad.Writer
import           Control.Monad.State
import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix
import           Data.List
import           Data.Function
import           Control.Lens

type Eqn ix pat = (ix, (pat, pat))

pattern Equated ix left right = (ix, (left, right))

type UnificationBag ix pat = (S.Set (Eqn ix pat), S.Set (Eqn ix pat))

data AdHocRules ix
  = NoConfusion ix
  | AndL ix
  | AndR ix
  | Transitive ix ix -- a = b, a = c ----> b = c
  | Assumption

data UnificationState ix pat
  = UnificationState
  { _activeSet :: UnificationBag ix pat 
  , _proof     :: Proof ix AdHocRules (pat, pat)
  }

makeLenses ''UnificationState

type UnificationContext ix pat level m
  = ( Ord ix , Ord pat
  , MonadState (UnificationState ix pat) m
  , MonadError (UnificationError level) m
  ) 

splitConstructor 
  :: UnificationContext ix pat level m
  => MetadataTools level
  -> Eqn ix pat
  -> m (S.Set (Eqn ix pat))
splitConstructor tools (ix, (left, right))
  | left == right 
      = return S.empty
  | not undefined --(isConstructor tools headLeft)
      = throwError $ undefined --NonConstructorHead headLeft
  | not undefined --(isConstructor tools headRight)
      = throwError $ undefined --NonConstructorHead headRight
  | headLeft /= headRight
      = throwError $ undefined --ConstructorClash headLeft headRight
  | otherwise
      = equateChildren (ix, (left, right))
    where 
      headLeft  = getHead left -- applicationSymbolOrAlias $ unFix left
      headRight = getHead right --applicationSymbolOrAlias $ unFix right

getHead = id

equateChildren
  :: UnificationContext ix pat level m
  => Eqn ix pat
  -> m (S.Set (Eqn ix pat))
equateChildren (ix, (left, right)) = do
  (ix', _) <- useNoConfusion ix
  eqns <- splitConjunction ix'
  return $ S.fromList eqns

-- These funcs take the index of a proposition
-- and deduce something from them

-- given the index of a prop of the form C(a1,...,an) = C(b1,...,bn)
-- applies no confusion for that constructor 
-- and returns the index of new prop a1 = b1 /\ ... /\ an = bn
useNoConfusion ix = undefined
splitConjunction 
  :: UnificationContext ix pat level m
  => ix 
  -> m [ Eqn ix pat ]
splitConjunction ix = do
  p <- use proof
  let Just line = M.lookup ix p
  case line of
    isConjunction -> do
      let leftProp  = andL ix p
      let rightProp = andR ix p
      let (ixL, p')  = addLine leftProp  p
      let (ixR, p'') = addLine rightProp p
      proof .= p''
      ixL' <- splitConjunction ixL 
      ixR' <- splitConjunction ixR
      return (union ixL' ixR')
    isntConjunction -> return [(ix, claim line)]

andL ix proof =
  Line 
 { claim = undefined $ claim line
 , justification = AndL ix
 , assumptions = assumptions line
 } where Just line = M.lookup ix proof

andR ix proof =
  Line 
 { claim = undefined $ claim line
 , justification = AndR ix
 , assumptions = assumptions line
 } where Just line = M.lookup ix proof


-- (varEqns, otherEqns)
-- varEqns holds only equations of the form x = t, where x is a variable
-- -- otherEqns holds arbitrary equations, waiting to be processed

step 
  :: UnificationContext ix pat level m
  => MetadataTools level
  -> m Bool
step tools = do
  (varEqns, otherEqns) <- use activeSet
  case S.maxView otherEqns of
    Nothing -> handleVarEqns
    Just (eqn, rest)
      | isVarEqn eqn -> do
          activeSet .= (S.insert (orient eqn) varEqns, rest)
          return False
      | otherwise -> do
           splitCons <- splitConstructor tools eqn
           activeSet .= (varEqns, S.union splitCons rest)
           return False

isVarEqn = undefined
orient = undefined


handleVarEqns
  :: UnificationContext ix pat level m
  => m Bool
handleVarEqns = do
  (varEqns, otherEqns) <- use activeSet
  forM_ varEqns occursCheck
  let eqns = groupBy sameVariable $ S.elems varEqns
  newEqns <- forM eqns reArrange
  activeSet .= (S.empty, S.fromList $ concat $ newEqns)
  return (length eqns == S.size varEqns)


-- reArrange transforms:
-- x = t1, x = t2, x = t3
-- into:
-- x = t1, t1 = t2, t2 = t3
-- slightly different from using x = (t1 /\ t2)
-- accomplishes the same thing
-- much easier to work with, IMO
reArrange [eqn] = return [eqn]
reArrange (eqn : es) = (eqn :) <$> go ix es
  where (ix, _) = eqn
        go ix (eqn : es) = do
          let (ix', (left, right)) = eqn
          eqn' <- useTransitivity ix ix'
          (eqn' :) <$> go ix' es
        go _ [] = return []

-- useTransitivity:
-- ix  : a = b
-- ix' : a = c
-- returns index of new prop, b = c
useTransitivity ix ix' = undefined

occursCheck = undefined

sameVariable a b = (getVariable a) == (getVariable b)
getVariable :: Eqn ix pat -> pat
getVariable = undefined
-- getVariable (ix, (Fix (VariablePattern vp, right))) = vp 

unify
  :: UnificationContext ix pat level m
  => MetadataTools level
  -> Eqn ix pat
  -> m ()
unify tools eqn@(ix, (left, right)) = do
  activeSet .= (S.empty, S.singleton eqn)
  loop
    where loop = do
            done <- step tools
            if done then return () else loop