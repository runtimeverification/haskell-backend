{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.FreshVariables.Class where

import           Control.Monad.Reader (ReaderT, lift)

import           Data.Kore.AST

class (Monad m, VariableClass var) => FreshVariables m var where
    freshVariable :: IsMeta a => var a -> m (var a)
    freshUnifiedVariable :: UnifiedVariable var -> m (UnifiedVariable var)
    freshUnifiedVariable = transformUnifiedVariable
        (\v -> asUnifiedVariable <$> freshVariable v)
    freshVariableSuchThat
        :: UnifiedVariable var
        -> (UnifiedVariable var -> Bool)
        -> m (UnifiedVariable var)
    freshVariableSuchThat var p = do
        var' <- freshUnifiedVariable var
        if p var'
            then return var'
            else error "Cannot generate variable satisfying predicate"

instance FreshVariables m var => FreshVariables (ReaderT a m) var where
    freshVariable = lift . freshVariable

