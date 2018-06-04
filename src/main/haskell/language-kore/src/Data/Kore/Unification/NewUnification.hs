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

module Data.Kore.Unification.NewUnification where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML
import           Data.Kore.FixTraversals
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.Unification.Error

import           Control.Monad.Except
import           Control.Monad.Writer
import           Control.Monad.State
import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix
import           Data.List
import           Data.Function

replace f x = S.union (f x) . S.delete x 


splitConstructor :: 
  ( Ord ix
  , MonadState (UnificationBag ix (T level)) m
  , MonadWriter () m
  , MonadError (UnificationError level) m) 
  => MetadataTools level
  -> Eqn ix level
  -> m (S.Set (Eqn ix pat))
splitConstructor tools (ix, (left, right))
  | left == right 
      = return S.empty
  | not (isConstructor tools headLeft)
      = throwError $ NonConstructorHead headLeft
  | not (isConstructor tools headRight)
      = throwError $ NonConstructorHead headRight
  | headLeft /= headRight
      = throwError $ ConstructorClash headLeft headRight
  | otherwise
      = equateChildren (ix, (left, right))
    where 
      headLeft  = applicationSymbolOrAlias $ unFix left
      headRight = applicationSymbolOrAlias $ unFix right

equateChildren :: 
  ( Ord ix
  , MonadState (UnificationBag ix (T level)) m
  , MonadWriter () m
  , MonadError (UnificationError level) m) 
  => Eqn ix level
  -> m (S.Set (Eqn ix pat))
equateChildren (ix, (left, right)) = do
  (ix', _) <- useNoConfusion ix
  eqns <- splitConjunction ix'
  return $ S.fromList eqns

type Eqn ix level = (ix, (T level, T level))

type T level = UnFixedPureMLPattern level Variable

type UnificationBag ix pat = (S.Set (Eqn ix pat), S.Set (Eqn ix pat))

-- (varEqns, otherEqns)
-- varEqns holds only equations of the form x = t, where x is a variable
-- -- otherEqns holds arbitrary equations, waiting to be processed

-- step :: 
--   ( Ord ix , Ord pat
--   , MonadState (UnificationBag ix pat) m
--   , MonadWriter () m
--   , MonadError (UnificationError level) m) 
--   => MetadataTools level
--   -> m ()
-- step tools = do
--   (varEqns, otherEqns) <- get
--   case S.maxView otherEqns of
--     Nothing -> handleVarEqns
--     Just (eqn, rest)
--       | isVarEqn eqn ->
--           put (S.insert (orient eqn) varEqns, rest)
--       | otherwise -> do
--            splitCons <- splitConstructor tools eqn
--            put (varEqns, S.union splitCons rest)

-- handleVarEqns = undefined
-- handleVarEqns = do
--   (varEqns, _) <- get
--   forM_ varEqns occursCheck
--   let eqns = groupBy sameVariable $ S.elems varEqns
--   undefined

-- occursCheck = undefined

-- sameVariable a b = (getVariable a) == (getVariable b)
-- getVariable = undefined
-- getVariable (ix, (Fix (VariablePattern vp, right))) = vp 

isVarEqn = undefined
orient = undefined

getLHS = undefined
getRHS = undefined

-- These funcs take the index of a proposition
-- and deduce something from them

-- given the index of a prop of the form C(a1,...,an) = C(b1,...,bn)
-- applies no confusion for that constructor 
-- and returns the index of new prop a1 = b1 /\ ... /\ an = bn
useNoConfusion ix = undefined
splitConjunction ix = undefined


  

-- checkFunctional tools (Fix (VariablePattern v)) 
--   = return $ FunctionalVariable v
-- checkFunctional tools (Fix (ApplicationPattern ap))
--   | isFunctional tools patternHead = do
--       functionalChildren <- mapM (checkFunctional tools) patternChildren
--       return $ FunctionalHeadAndChildren patternHead functionalChildren
--   | otherwise = throwError (NonFunctionalHead patternHead)
--       where patternHead     = applicationSymbolOrAlias ap
--             patternChildren = applicationChildren      ap