{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Variables.Fresh.Class where

import qualified Control.Monad.State                  as State

import           Data.Kore.AST
import           Data.Kore.Variables.Fresh.IntCounter
import           Data.Kore.Variables.Int

{-|'FreshVariablesClass' links a `VariableClass` representing a type of
variables with a 'Monad' containing state needed to generate fresh variables
and provides several functions to generate new variables.
-}
class (Monad m, VariableClass var) => FreshVariablesClass m var where
    {-|Given an existing variable, generate a fresh one of
    the same type and sort.
    -}
    freshVariable :: IsMeta a => var a -> m (var a)
    {-|Given an existing variable, generate a fresh unified one of
    the same type and sort.
    -}
    variableToFreshUnified :: IsMeta a => var a -> m (UnifiedVariable var)
    variableToFreshUnified = fmap asUnified . freshVariable
    {-|Given an existing unified variable, generate a fresh one of
    the same type and sort.
    -}
    freshUnifiedVariable :: UnifiedVariable var -> m (UnifiedVariable var)
    freshUnifiedVariable = transformUnified variableToFreshUnified

    {-|Given an existing 'UnifiedVariable' and a predicate, generate a
    fresh 'UnifiedVariable' of the same type and sort satisfying the predicate.
    By default, die in flames if the predicate is not satisfied.
    -}
    freshVariableSuchThat
        :: UnifiedVariable var
        -> (UnifiedVariable var -> Bool)
        -> m (UnifiedVariable var)
    freshVariableSuchThat var p = do
        var' <- freshUnifiedVariable var
        if p var'
            then return var'
            else error "Cannot generate variable satisfying predicate"

instance (State.MonadTrans t, Monad (t m), FreshVariablesClass m var)
    => FreshVariablesClass (t m) var
  where
    freshVariable = State.lift . freshVariable

instance IntVariable var
    => FreshVariablesClass IntCounter var
  where
    freshVariable var = do
        counter <- State.get
        State.modify (+1)
        return (intVariable var counter)
