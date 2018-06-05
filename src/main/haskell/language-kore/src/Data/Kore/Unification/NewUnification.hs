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
import           Data.Kore.AST.MetaOrObject
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


{-

ACHTUNG!

Everything here is very sloppy and preliminary.

Type params 'level' and 'pat' have been fixed to an arbitrary value
to avoid type errors. 

All the state monad stuff with Proof should be refactored.

-}
type Pat = PureMLPattern Meta Variable

type Eqn ix pat = (ix, Pat)

pattern Equated ix s1 s2 left right = (ix, Fix (EqualsPattern (Equals s1 s2 left right)))

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
  , _proof     :: Proof ix AdHocRules pat
  }

makeLenses ''UnificationState

type UnificationContext ix pat level m
  = ( Ord ix -- , Ord Pat, Eq Pat
  , MonadState (UnificationState ix Pat) m
  , MonadError (UnificationError Meta) m
  ) 

splitConstructor 
  :: UnificationContext ix pat level m
  => MetadataTools Meta
  -> Eqn ix pat
  -> m (S.Set (Eqn ix pat))
splitConstructor tools (Equated ix s1 s2 left right)
  | left == right 
      = return S.empty
  | not (isConstructor tools headLeft)
      = throwError $ NonConstructorHead headLeft
  | not (isConstructor tools headRight)
      = throwError $ NonConstructorHead headRight
  | headLeft /= headRight
      = throwError $ ConstructorClash headLeft headRight
  | otherwise
      = equateChildren (Equated ix s1 s2 left right)
    where 
      ApplicationPattern (Application headLeft  _) = unFix left
      ApplicationPattern (Application headRight _) = unFix right

-- getHead = id

equateChildren
  :: UnificationContext ix pat level m
  => Eqn ix pat
  -> m (S.Set (Eqn ix pat))
equateChildren (Equated ix s1 s2 left right) = do
  (ix', _) <- useNoConfusion ix
  eqns <- splitConjunction ix'
  return $ S.fromList eqns

-- These funcs take the index of a proposition
-- and deduce something from them

-- given the index of a prop of the form C(a1,...,an) = C(b1,...,bn)
-- applies no confusion for that constructor 
-- and returns the index of new prop a1 = b1 /\ ... /\ an = bn
useNoConfusion ix = do
  p <- use proof
  let Just line = M.lookup ix p
  let line' = 
        Line
        { claim = undefined
        , justification = NoConfusion ix --false, there is plenty of confusion
        , assumptions = assumptions line 
        }
  let (ix',p') = addLine line' p
  proof .= p
  return (ix', claim line)

splitConjunction 
  :: UnificationContext ix pat level m
  => ix 
  -> m [ Eqn ix pat ]
splitConjunction ix = do
  p <- use proof
  let Just line = M.lookup ix p
  case claim line of
    IsConjunction _ _ -> do
      let leftProp  = andL ix p
      let rightProp = andR ix p
      let (ixL, p')  = addLine leftProp  p
      let (ixR, p'') = addLine rightProp p
      proof .= p''
      ixL' <- splitConjunction ixL 
      ixR' <- splitConjunction ixR
      return (union ixL' ixR')
    _ -> return [(ix, claim line)]

pattern IsConjunction a b <- Fix (AndPattern (And _ a b))

andL ix proof =
  Line 
 { claim = getAndL $ claim line
 , justification = AndL ix
 , assumptions = assumptions line
 } where Just line = M.lookup ix proof

getAndL (Fix (AndPattern x)) = andFirst x

andR ix proof =
  Line 
 { claim = getAndR $ claim line
 , justification = AndR ix
 , assumptions = assumptions line
 } where Just line = M.lookup ix proof

getAndR (Fix (AndPattern x)) = andSecond x

-- (varEqns, otherEqns)
-- varEqns holds only equations of the form x = t, where x is a variable
-- -- otherEqns holds arbitrary equations, waiting to be processed

step 
  :: UnificationContext ix pat level m
  => MetadataTools Meta
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

isVarEqn (_, Fix (EqualsPattern (Equals s1 s2 left right)))
 = isVar left || isVar right

isVar (Fix (VariablePattern _)) = True
isVar _ = False

orient (ix, Fix (EqualsPattern (Equals s1 s2 left right))) = 
  if isVar left
  then (ix, Fix (EqualsPattern (Equals s1 s2 left right)))
  else (ix, Fix (EqualsPattern (Equals s1 s2 right left))) --FIXME: Use symmetry axiom


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
          let (Equated ix' s1 s2 left right) = eqn
          eqn' <- useTransitivity ix ix'
          (eqn' :) <$> go ix' es
        go _ [] = return []

-- useTransitivity:
-- ix  : a = b
-- ix' : a = c
-- returns index of new prop, b = c
useTransitivity ix1 ix2 = do
  p <- use proof
  let Just line1 = M.lookup ix1 p
  let Just line2 = M.lookup ix2 p
  let line3 = 
        Line
        { claim = undefined
        , justification = Transitive ix1 ix2
        , assumptions = assumptions line1 `S.union` assumptions line2
        }
  let (ix3, p') = addLine line3 p
  proof .= p'
  return (ix3, claim line3)


occursCheck = return () --FIXME: 

sameVariable a b = (getVariable a) == (getVariable b)
getVariable (Equated ix s1 s2 left right) = left
-- getVariable (ix, (Fix (VariablePattern vp, right))) = vp 

unify
  :: UnificationContext ix pat level m
  => MetadataTools Meta
  -> Eqn ix pat
  -> m ()
unify tools eqn@(Equated ix s1 s2 left right) = do
  activeSet .= (S.empty, S.singleton eqn)
  loop
    where loop = do
            done <- step tools
            if done then return () else loop