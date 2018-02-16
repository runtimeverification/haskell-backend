{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Substitution.Class ( SubstitutionClass (..)
                                    , PatternSubstitutionClass (..)
                                    ) where

import           Control.Monad.Reader            (ReaderT, ask, runReaderT,
                                                  withReaderT)
import           Data.Maybe                      (isJust)
import qualified Data.Set                        as Set
import           Prelude                         hiding (lookup)

import           Data.Kore.AST
import           Data.Kore.ASTTraversals         (topDownVisitorM)
import           Data.Kore.Variables.Free
import           Data.Kore.Variables.Fresh.Class

class SubstitutionClass s v t | s -> v, s -> t where
    isEmpty :: s -> Bool
    lookup :: Eq v => v -> s -> Maybe t
    getFreeVars :: s -> Set.Set v
    addBinding :: v -> t -> s -> s
    removeBinding :: v -> s -> s

data SubstitutionWithFreeVars s var = SubstitutionWithFreeVars
    { substitution :: s
    , freeVars     :: Set.Set (UnifiedVariable var)
    }

addFreeVariable
    :: Ord (UnifiedVariable var)
    => UnifiedVariable var
    -> SubstitutionWithFreeVars s var
    -> SubstitutionWithFreeVars s var
addFreeVariable v s = s { freeVars = v `Set.insert` freeVars s }

instance ( VariableClass var
         , SubstitutionClass s (UnifiedVariable var) (FixedPattern var)
         ) => SubstitutionClass (SubstitutionWithFreeVars s var)
        (UnifiedVariable var) (FixedPattern var) where
    isEmpty s = isEmpty (substitution s)
    lookup v s = lookup v (substitution s)
    removeBinding v s = s { substitution = removeBinding v (substitution s) }
    addBinding v t s =
        s { substitution = addBinding v t (substitution s)
          , freeVars = freeVars s `Set.union` freeVariables t
          }
    getFreeVars = freeVars

class ( SubstitutionClass s (UnifiedVariable var) (FixedPattern var)
      , FreshVariablesClass m var
      ) => PatternSubstitutionClass var s m where
    substitute
        :: FixedPattern var
        -> s
        -> m (FixedPattern var)
    substitute p s = runReaderT (substituteM p) SubstitutionWithFreeVars
        { substitution = s
        , freeVars =
            freeVariables p `Set.union` getFreeVars s
        }

substituteM
    :: PatternSubstitutionClass var s m
    => FixedPattern var
    -> ReaderT (SubstitutionWithFreeVars s var) m (FixedPattern var)
substituteM = topDownVisitorM substitutePreprocess substituteVariable

substituteVariable
    :: (IsMeta a, PatternSubstitutionClass var s m)
    => Pattern a var (FixedPattern var)
    -> ReaderT (SubstitutionWithFreeVars s var) m (FixedPattern var)
substituteVariable (VariablePattern v) = do
    subst <- substitution <$> ask
    case lookup (asUnifiedVariable v) subst of
        Just up -> return up
        Nothing -> return $ asUnifiedPattern (VariablePattern v)
substituteVariable p = return $ asUnifiedPattern p

substitutePreprocess
    :: (IsMeta a, PatternSubstitutionClass var s m)
    => Pattern a var (FixedPattern var)
    -> ReaderT (SubstitutionWithFreeVars s var)
        m (Either (FixedPattern var) (Pattern a var (FixedPattern var)))
substitutePreprocess p = do
    s <- ask
    if isEmpty s then return $ Left (asUnifiedPattern p)
    else case p of
        ExistsPattern e ->
            substituteCheckBinder s
                (\ srt var pat -> ExistsPattern (Exists srt var pat))
                (existsSort e) (existsVariable e) (existsPattern e)
        ForallPattern e ->
            substituteCheckBinder s
                (\ srt var pat -> ForallPattern (Forall srt var pat))
                (forallSort e) (forallVariable e) (forallPattern e)
        _ -> return $ Right p

substituteCheckBinder
    :: (PatternSubstitutionClass var s m, IsMeta a)
    => SubstitutionWithFreeVars s var
    -> (Sort a -> UnifiedVariable var -> FixedPattern var
        -> Pattern a var (FixedPattern var))
    -> Sort a
    -> UnifiedVariable var
    -> FixedPattern var
    -> ReaderT (SubstitutionWithFreeVars s var)
        m (Either (FixedPattern var) (Pattern a var (FixedPattern var)))
substituteCheckBinder s binder sort var pat
    | var `Set.member` vars = do
        var' <- freshVariableSuchThat var (not . (`Set.member` vars))
        pat' <- withReaderT (addBinding var (unifiedVariableToPattern var'))
            (substituteM pat)
        return $ Left $ asUnifiedPattern $ binder sort var' pat'
    | isJust (lookup var s) =
        substituteBinderBody (removeBinding var)
    | otherwise = substituteBinderBody id
  where
    vars = getFreeVars s
    substituteBinderBody fs = do
        pat' <- withReaderT (addFreeVariable var . fs)
            (substituteM pat)
        return $ Left $ asUnifiedPattern $ binder sort var pat'
