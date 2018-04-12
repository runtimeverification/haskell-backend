{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Kore.Variables.Fresh.Class where

import qualified Control.Monad.State as State

import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Variables.Fresh.IntCounter
import           Data.Kore.Variables.Int

{-|'FreshVariablesClass' links @var@ representing a type of variables
with a 'Monad' @m@ containing state needed to generate fresh
variables and provides several functions to generate new variables.
-}
class (Monad m, VariableClass var) =>
      FreshVariablesClass m var
    {-|Given an existing variable, generate a fresh one of
    the same kind.
    -}
  where
    freshVariable :: MetaOrObject level => var level -> m (var level)
    {-|Given an existing variable and a predicate, generate a
    fresh variable of the same kind satisfying the predicate.
    By default, die in flames if the predicate is not satisfied.
    -}
    freshVariableSuchThat
        :: MetaOrObject level
        => var level
        -> (var level -> Bool)
        -> m (var level)
    freshVariableSuchThat var p = do
        var' <- freshVariable var
        if p var'
            then return var'
            else error "Cannot generate variable satisfying predicate"

instance
    (State.MonadTrans t, Monad (t m), FreshVariablesClass m var)
    => FreshVariablesClass (t m) var
  where
    freshVariable = State.lift . freshVariable

instance
    (IntVariable var, VariableClass var)
    => FreshVariablesClass IntCounter var
  where
    freshVariable var = do
        counter <- State.get
        State.modify (+ 1)
        return (intVariable var counter)
