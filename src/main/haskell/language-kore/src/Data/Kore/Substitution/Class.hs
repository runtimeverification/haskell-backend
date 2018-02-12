{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Substitution.Class where

import           Data.Foldable           (foldrM)
import           Data.Maybe              (isJust)
import           Prelude                 hiding (lookup)

import           Data.Kore.AST
import           Data.Kore.ASTTraversals (freeVariables, topDownVisitorM)

class (Monad m, VariableClass var) => FreshVarGen m var | m -> var where
    freshVar :: IsMeta a => var a -> m (var a)
    freshVarNotInList :: IsMeta a => var a -> [UnifiedVariable var] -> m (var a)
    freshVarNotInList a vars = self
      where
        self = do
            var <- freshVar a
            if asUnifiedVariable var `Prelude.elem` vars
                then self
                else return var

class Substitution s where
    elem :: Eq v => v -> s v t -> Bool
    elem v s = isJust (lookup v s)
    lookup :: Eq v => v -> s v t -> Maybe t
    fromList :: Eq v => [(v,t)] -> s v t
    toList :: s v t -> [(v,t)]

class (Substitution s, FreshVarGen m var) => PatternSubstitution var s m where
    substitute
        :: FixedPattern var
        -> s (UnifiedVariable var) (FixedPattern var)
        -> m (FixedPattern var)
    substitute p s = foldrM substituteOne p (toList s)

substituteOne
    :: (FreshVarGen m var)
    => (UnifiedVariable var, FixedPattern var)
    -> (FixedPattern var -> m (FixedPattern var))
substituteOne s = topDownVisitorM (binderCheck s) (substituteVisitor s)

substituteVisitor
    :: (IsMeta a, FreshVarGen m var)
    => (UnifiedVariable var, FixedPattern var)
    -> Pattern a var (FixedPattern var)
    -> m (FixedPattern var)
substituteVisitor (uv, up) (VariablePattern v)
    | uv == asUnifiedVariable v = return up
    | otherwise = return $ asUnifiedPattern (VariablePattern v)
substituteVisitor _ p = return $ asUnifiedPattern p

binderCheck
    :: (IsMeta a, FreshVarGen m var)
    => (UnifiedVariable var, FixedPattern var)
    -> Pattern a var (FixedPattern var)
    -> m (Either (FixedPattern var) (Pattern a var (FixedPattern var)))
binderCheck (uv, _) ep@(ExistsPattern e)
    | uv == uev = return $ Left (asUnifiedPattern ep)
    | uev `Prelude.elem` vars = do
        var <- case uev of
            MetaVariable v   -> asUnifiedVariable <$> freshVarNotInList v vars
            ObjectVariable v -> asUnifiedVariable <$> freshVarNotInList v vars
        p <- substituteOne (uev, unifiedVariableToPattern var) (existsPattern e)
        return $ Right $ ExistsPattern $ e { existsVariable = var
                 , existsPattern = p }
  where
    uev = existsVariable e
    vars = freeVariables (asUnifiedPattern ep)
binderCheck (uv, _) fp@(ForallPattern e)
    | uv == forallVariable e = return $ Left (asUnifiedPattern fp)
binderCheck _ p = return $ Right p
