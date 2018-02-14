{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Substitution.Class ( Substitution (..)
                                    , PatternSubstitution (..)
                                    ) where

import           Control.Monad.Reader           (ReaderT, ask, runReaderT,
                                                 withReaderT)
import           Data.Maybe                     (isJust)
import qualified Data.Set                       as Set
import           Prelude                        hiding (lookup)

import           Data.Kore.AST
import           Data.Kore.ASTTraversals        (freeVariables, topDownVisitorM)
import           Data.Kore.FreshVariables.Class

class Substitution s v t | s -> v, s -> t where
    isEmpty :: s -> Bool
    lookup :: Eq v => v -> s -> Maybe t
    fromList :: Eq v => [(v,t)] -> s
    toList :: s -> [(v,t)]
    addBinding :: v -> t -> s -> s
    removeBinding :: v -> s -> s

data SubstitutionWithFreeVars s var = SubstitutionWithFreeVars
    { substitution :: s
    , freeVars     :: Set.Set (UnifiedVariable var)
    }

instance ( VariableClass var
         , Substitution s (UnifiedVariable var) (FixedPattern var)
         ) => Substitution (SubstitutionWithFreeVars s var)
        (UnifiedVariable var) (FixedPattern var) where
    isEmpty s = isEmpty (substitution s)
    lookup v s = lookup v (substitution s)
    fromList l = SubstitutionWithFreeVars
        { substitution = fromList l
        , freeVars = foldMap (freeVariables . snd) l
        }
    toList s = toList (substitution s)
    removeBinding v s = s { substitution = removeBinding v (substitution s) }
    addBinding v t s =
        s { substitution = addBinding v t (substitution s)
          , freeVars = freeVars s `Set.union` freeVariables t
          }

class ( Substitution s (UnifiedVariable var) (FixedPattern var)
      , FreshVariablesClass m var
      ) => PatternSubstitution var s m where
    substitute
        :: FixedPattern var
        -> s
        -> m (FixedPattern var)
    substitute p s = runReaderT (substituteM p) SubstitutionWithFreeVars
        { substitution = s
        , freeVars = foldMap (freeVariables . snd) (toList s)
        }

substituteM
    :: PatternSubstitution var s m
    => FixedPattern var
    -> ReaderT (SubstitutionWithFreeVars s var) m (FixedPattern var)
substituteM = topDownVisitorM substitutePreprocess substituteVariable

substituteVariable
    :: (IsMeta a, PatternSubstitution var s m)
    => Pattern a var (FixedPattern var)
    -> ReaderT (SubstitutionWithFreeVars s var) m (FixedPattern var)
substituteVariable (VariablePattern v) = do
    subst <- substitution <$> ask
    case lookup (asUnifiedVariable v) subst of
        Just up -> return up
        Nothing -> return $ asUnifiedPattern (VariablePattern v)
substituteVariable p = return $ asUnifiedPattern p

substitutePreprocess
    :: (IsMeta a, PatternSubstitution var s m)
    => Pattern a var (FixedPattern var)
    -> ReaderT (SubstitutionWithFreeVars s var)
        m (Either (FixedPattern var) (Pattern a var (FixedPattern var)))
substitutePreprocess p = do
    s <- ask
    if isEmpty (substitution s) then return $ Left (asUnifiedPattern p)
    else case p of
        ExistsPattern e ->
            substituteCheckBinder s (((ExistsPattern .) .) . Exists)
                (existsSort e) (existsVariable e) (existsPattern e)
        ForallPattern e ->
            substituteCheckBinder s (((ForallPattern .) .) . Forall)
                (forallSort e) (forallVariable e) (forallPattern e)
        _ -> return $ Right p

substituteCheckBinder
    :: (PatternSubstitution var s m, IsMeta a)
    => SubstitutionWithFreeVars s var
    -> (Sort a -> UnifiedVariable var -> FixedPattern var
        -> Pattern a var (FixedPattern var))
    -> Sort a
    -> UnifiedVariable var
    -> FixedPattern var
    -> ReaderT (SubstitutionWithFreeVars s var)
        m (Either (FixedPattern var) (Pattern a var (FixedPattern var)))
substituteCheckBinder s binder sort var pat
    | isJust (lookup var (substitution s)) = do
        pat' <- withReaderT (removeBinding var)
            (substituteM pat)
        return $ Left $ asUnifiedPattern $ binder sort var pat'
    | var `Set.member` vars = do
        var' <- freshVariableSuchThat var (not . (`Set.member` vars))
        pat' <- withReaderT (addBinding var (unifiedVariableToPattern var'))
            (substituteM pat)
        return $ Left $ asUnifiedPattern $ binder sort var' pat'
    | otherwise = return $ Right $ binder sort var pat
  where
    vars = freeVars s
