{-|
Module      : Kore.Variables.Fresh.Class
Description : Specifies the 'FreshVariableClass' which provides an interface for
              generating fresh variables.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Variables.Fresh.Class where

import qualified Control.Monad.State as State

import Kore.AST.MetaOrObject
import Kore.Variables.Fresh.IntCounter
import Kore.Variables.Int

{-|'FreshVariablesClass' links @var@ representing a type of variables
with a 'Monad' @m@ containing state needed to generate fresh
variables and provides several functions to generate new variables.
-}
class (Monad m) => FreshVariablesClass m var where
    {-|Given an existing variable, generate a fresh one of
    the same kind.
    -}
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

instance (State.MonadTrans t, Monad (t m), FreshVariablesClass m var)
    => FreshVariablesClass (t m) var
  where
    freshVariable = State.lift . freshVariable

instance (IntVariable var)
    => FreshVariablesClass IntCounter var
  where
    freshVariable var = do
        counter <- State.get
        State.modify (+1)
        return (intVariable var counter)
