{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.Class ( SubstitutionClass (..)
                                    , PatternSubstitutionClass (..)
                                    ) where

import           Control.Monad.Reader              (ReaderT, ask, asks, local,
                                                    runReaderT)
import           Data.Hashable                     (hash)
import           Data.Maybe                        (isJust)
import qualified Data.Set                          as Set
import           Prelude                           hiding (lookup)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.MLPatterns
import           Data.Kore.ASTTraversals           (koreTopDownVisitorM)
import           Data.Kore.Datastructures.MapClass
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
    , quantifiedVars :: Set.Set (Unified var)
    }

addFreeVariable
    :: (Ord (var Object), Ord (var Meta))
    => Unified var
    -> SubstitutionAndQuantifiedVars s var
    -> SubstitutionAndQuantifiedVars s var
addFreeVariable v s = s { quantifiedVars = v `Set.insert` quantifiedVars s }

instance (SubstitutionClass s (Unified var) (KorePattern var))
    => MapClass (SubstitutionAndQuantifiedVars s var)
        (Unified var) (KorePattern var)
  where
    isEmpty = isEmpty . substitution
    empty = SubstitutionAndQuantifiedVars
        { substitution = empty
        , quantifiedVars = Set.empty
        }
    lookup v = lookup v . substitution
    delete v s = s { substitution = delete v (substitution s) }
    insert v t s =
        s { substitution = insert v t (substitution s) }

instance (SubstitutionClass s (Unified var) (KorePattern var))
    => SubstitutionClass (SubstitutionAndQuantifiedVars s var)
        (Unified var) (KorePattern var)
  where
    substitutionTermsFreeVars = substitutionTermsFreeVars . substitution

class Hashable var where
    getVariableHash :: var level -> Int

instance Hashable Variable where
    getVariableHash = hash . getId . variableName

{-|'PatternSubstitutionClass' defines a generic 'substitute' function
which given a 'FixedPattern' @p@ and an @s@ of class 'SubstitutionClass',
applies @s@ on @p@ in a monadic state used for generating fresh variables.
-}
class ( SubstitutionClass s (Unified var) (KorePattern var)
      , FreshVariablesClass m var
      , Ord (var Meta)
      , Ord (var Object)
      , Hashable var
      )
    => PatternSubstitutionClass var s m
  where
    substitute
        :: KorePattern var
        -> s
        -> m (KorePattern var)
    substitute p s = runReaderT (substituteM p) SubstitutionAndQuantifiedVars
        { substitution = s
        , quantifiedVars = freeVariables p
        }

substituteM
    :: PatternSubstitutionClass var s m
    => KorePattern var
    -> ReaderT (SubstitutionAndQuantifiedVars s var) m (KorePattern var)
substituteM = koreTopDownVisitorM substitutePreprocess substituteVariable

substituteVariable
    :: (PatternSubstitutionClass var s m, MetaOrObject level)
    => Pattern level var (KorePattern var)
    -> ReaderT (SubstitutionAndQuantifiedVars s var) m (KorePattern var)
substituteVariable (VariablePattern v) = do
    subst <- asks substitution
    case lookup (asUnified v) subst of
        Just up -> return up
        Nothing -> return $ asKorePattern (VariablePattern v)
substituteVariable p = return $ asKorePattern p

{-
* if the substitution is empty, return the pattern unchanged;
* if the pattern is a binder, handle using 'binderPatternSubstitutePreprocess'
* if the pattern is not a binder recurse.
-}
substitutePreprocess
    :: (PatternSubstitutionClass var s m, MetaOrObject level)
    => Pattern level var (KorePattern var)
    -> ReaderT (SubstitutionAndQuantifiedVars s var)
        m (Either
            (KorePattern var)
            ( Pattern level var (KorePattern var)
            , ReaderT (SubstitutionAndQuantifiedVars s var) m (KorePattern var)
                -> ReaderT
                    (SubstitutionAndQuantifiedVars s var)
                    m (KorePattern var)
            )
        )
substitutePreprocess p
  = do
    s <- ask
    if isEmpty s then return $ Left (asKorePattern p)
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
    :: ( MLBinderPatternClass q
       , PatternSubstitutionClass var s m
       , MetaOrObject level)
    => SubstitutionAndQuantifiedVars s var
    -> q level var (KorePattern var)
    -> ReaderT (SubstitutionAndQuantifiedVars s var)
        m (Either
            (KorePattern var)
            ( Pattern level var (KorePattern var)
            , ReaderT (SubstitutionAndQuantifiedVars s var) m (KorePattern var)
                -> ReaderT (SubstitutionAndQuantifiedVars s var)
                    m (KorePattern var)
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
            (insert unifiedVar (variableToKorePattern var'))
    | isJust (lookup unifiedVar s) = substituteFreeBinderBodyWith (delete unifiedVar)
    | otherwise = substituteFreeBinderBodyWith id
  where
    sort = getBinderPatternSort q
    var = getBinderPatternVariable q
    unifiedVar = asUnified var
    variableToKorePattern = asKorePattern . VariablePattern
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
