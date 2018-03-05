{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.Class ( SubstitutionClass (..)
                                    , PatternSubstitutionClass (..)
                                    ) where

import           Control.Monad.Reader            (ReaderT, ask, local,
                                                  runReaderT)
import           Data.Maybe                      (isJust)
import qualified Data.Set                        as Set
import           Prelude                         hiding (lookup)

import           Data.Kore.AST
import           Data.Kore.ASTTraversals         (topDownVisitorM)
import           Data.Kore.Substitution.MapClass
import           Data.Kore.Variables.Free
import           Data.Kore.Variables.Fresh.Class

{-|'SubstitutionClass' represents a substitution type @s@ mapping variables
of type @v@ to terms of type @t@.
-}
class MapClass s v t => SubstitutionClass s v t where
    {-|Collects all free variables from the terms belonging to the
    image of the substitution.
    This can, e.g., be used to prevent collisions when generating
    fresh variables.
    -}
    substitutionTermsFreeVars :: s -> Set.Set v

{-'SubstitutionWithFreeVars' is a substitution which can hold more free
variables than its terms can.  'freeVars' is used to track the free variables
in a substitution context.
-}
data SubstitutionAndQuantifiedVars s var = SubstitutionAndQuantifiedVars
    { substitution   :: s
    , quantifiedVars :: Set.Set (UnifiedVariable var)
    }

addFreeVariable
    :: Ord (UnifiedVariable var)
    => UnifiedVariable var
    -> SubstitutionAndQuantifiedVars s var
    -> SubstitutionAndQuantifiedVars s var
addFreeVariable v s = s { quantifiedVars = v `Set.insert` quantifiedVars s }

instance ( VariableClass var
         , SubstitutionClass s (UnifiedVariable var) (FixedPattern var)
         )
    => MapClass (SubstitutionAndQuantifiedVars s var)
        (UnifiedVariable var) (FixedPattern var)
  where
    isEmpty = isEmpty . substitution
    lookup v = lookup v . substitution
    delete v s = s { substitution = delete v (substitution s) }
    insert v t s =
        s { substitution = insert v t (substitution s) }

instance ( VariableClass var
         , SubstitutionClass s (UnifiedVariable var) (FixedPattern var)
         )
    => SubstitutionClass (SubstitutionAndQuantifiedVars s var)
        (UnifiedVariable var) (FixedPattern var)
  where
    substitutionTermsFreeVars = substitutionTermsFreeVars . substitution

{-|'PatternSubstitutionClass' defines a generic 'substitute' function
which given a 'FixedPattern' @p@ and an @s@ of class 'SubstitutionClass',
applies @s@ on @p@ in a monadic state used for generating fresh variables.
-}
class ( SubstitutionClass s (UnifiedVariable var) (FixedPattern var)
      , FreshVariablesClass m var
      )
    => PatternSubstitutionClass var s m
  where
    substitute
        :: FixedPattern var
        -> s
        -> m (FixedPattern var)
    substitute p s = runReaderT (substituteM p) SubstitutionAndQuantifiedVars
        { substitution = s
        , quantifiedVars = freeVariables p
        }

substituteM
    :: PatternSubstitutionClass var s m
    => FixedPattern var
    -> ReaderT (SubstitutionAndQuantifiedVars s var) m (FixedPattern var)
substituteM = topDownVisitorM substitutePreprocess substituteVariable

substituteVariable
    :: (IsMeta a, PatternSubstitutionClass var s m)
    => Pattern a var (FixedPattern var)
    -> ReaderT (SubstitutionAndQuantifiedVars s var) m (FixedPattern var)
substituteVariable (VariablePattern v) = do
    subst <- substitution <$> ask
    case lookup (asUnified v) subst of
        Just up -> return up
        Nothing -> return $ asUnifiedPattern (VariablePattern v)
substituteVariable p = return $ asUnifiedPattern p

{-
* if the substitution is empty, return the pattern unchanged;
* if the pattern is a binder, handle using 'binderPatternSubstitutePreprocess'
* if the pattern is not a binder recurse.
-}
substitutePreprocess
    :: (IsMeta a, PatternSubstitutionClass var s m)
    => Pattern a var (FixedPattern var)
    -> ReaderT (SubstitutionAndQuantifiedVars s var)
        m (Either
            (FixedPattern var)
            ( Pattern a var (FixedPattern var)
            , ReaderT (SubstitutionAndQuantifiedVars s var) m (FixedPattern var)
                -> ReaderT (SubstitutionAndQuantifiedVars s var) m (FixedPattern var)
            )
        )
substitutePreprocess p
  = do
    s <- ask
    if isEmpty s then return $ Left (asUnifiedPattern p)
    else case p of
        ExistsPattern e -> binderPatternSubstitutePreprocess s e
        ForallPattern f -> binderPatternSubstitutePreprocess s f
        _               -> return $ Right (p, id)

{-
* if the quantified variable is among the encountered free variables
  in this contex, add an alpha-renaming binding to the substitution
* if the quantified variable is replaced by this substitution,
  susbtitute the body using the substitution without this variable
* otherwise, do a full substitution of the body (remembering that, in this
  context, the quantified variable is free).
-}
binderPatternSubstitutePreprocess
    :: (MLBinderPatternClass q, PatternSubstitutionClass var s m, IsMeta a)
    => SubstitutionAndQuantifiedVars s var
    -> q a var (FixedPattern var)
    -> ReaderT (SubstitutionAndQuantifiedVars s var)
        m (Either
            (FixedPattern var)
            ( Pattern a var (FixedPattern var)
            , ReaderT (SubstitutionAndQuantifiedVars s var) m (FixedPattern var)
                -> ReaderT (SubstitutionAndQuantifiedVars s var)
                    m (FixedPattern var)
            )
        )
binderPatternSubstitutePreprocess s q
    | unifiedVar `Set.member` substitutionFreeVars
      = do
        var' <- freshVariableSuchThat
            var
            ( not
            . (`Set.member` allFreeVarsIds)
            . getVariableHash
            )
        substituteBinderBodyWith var'
            (insert unifiedVar (variableToUnifiedPattern var'))
    | isJust (lookup unifiedVar s) = substituteFreeBinderBodyWith (delete unifiedVar)
    | otherwise = substituteFreeBinderBodyWith id
  where
    sort = getBinderPatternSort q
    var = getBinderPatternVariable q
    unifiedVar = asUnified var
    variableToUnifiedPattern = asUnifiedPattern . VariablePattern
    pat = getBinderPatternChild q
    substitutionFreeVars = substitutionTermsFreeVars (delete unifiedVar s)
    allFreeVars = substitutionFreeVars `Set.union` quantifiedVars s
    allFreeVarsIds =
        Set.map (transformUnified getVariableHash) allFreeVars
    substituteBinderBodyWith newVar fs =
        return
            (Right (binderPatternConstructor q sort newVar pat, local fs))
    substituteFreeBinderBodyWith fs =
        substituteBinderBodyWith var (addFreeVariable unifiedVar . fs)
