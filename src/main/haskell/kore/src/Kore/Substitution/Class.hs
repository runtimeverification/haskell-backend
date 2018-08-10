{-|
Module      : Kore.Substitution.Class
Description : Defines basic interfaces and main functionality needed
              to implement substitution for an 'UnifiedPatternInterface'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Substitution.Class
    ( SubstitutionClass (..)
    , PatternSubstitutionClass (..)
    , Hashable (..)
    ) where

import           Control.Monad.Reader
                 ( ReaderT, ask, asks, local, runReaderT )
import           Data.Functor.Foldable
import           Data.Hashable
                 ( hash )
import           Data.Maybe
                 ( isJust )
import qualified Data.Set as Set
import           Prelude hiding
                 ( lookup )

import Data.Map.Class
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.MLPatterns
import Kore.ASTTraversals
       ( patternTopDownVisitorM )
import Kore.Variables.Free
import Kore.Variables.Fresh.Class

{-|'SubstitutionClass' represents a substitution type @s@ mapping variables
of type @v@ to terms of type @t@.
-}
class MapClass s v t => SubstitutionClass s v t where
    {-|Collects all free variables from the terms belonging to the
    image of the substitution.
    This can, e.g., be used to prevent collisions when generating
    fresh variables.
    -}
    substitutionTermsFreeVars :: s v t -> Set.Set v

{-'SubstitutionAndQuantifiedVars' is a substitution which can hold more free
variables than its terms can.  'quantifiedVars' is used to track the free
variables in a substitution context.
-}
data SubstitutionAndQuantifiedVars s var pat = SubstitutionAndQuantifiedVars
    { substitution   :: s var pat
    , quantifiedVars :: Set.Set var
    }

type FixedSubstitutionAndQuantifiedVars s var pat =
    SubstitutionAndQuantifiedVars s (Unified var) (Fix (pat var))

addFreeVariable
    :: (Ord var)
    => var
    -> SubstitutionAndQuantifiedVars s var pat
    -> SubstitutionAndQuantifiedVars s var pat
addFreeVariable v s = s { quantifiedVars = v `Set.insert` quantifiedVars s }

instance (SubstitutionClass s var pat)
    => MapClass (SubstitutionAndQuantifiedVars s) var pat
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

instance (SubstitutionClass s var pat)
    => SubstitutionClass (SubstitutionAndQuantifiedVars s) var pat
  where
    substitutionTermsFreeVars = substitutionTermsFreeVars . substitution

class Hashable var where
    getVariableHash :: var level -> Int

instance Hashable Variable where
    getVariableHash = hash . getId . variableName

{-|'PatternSubstitutionClass' defines a generic 'substitute' function
which given a @p@ of the 'UnifiedPatternInterface' class
and an @s@ of 'SubstitutionClass', applies @s@ on @p@ in a monadic state
used for generating fresh variables.
-}
class ( UnifiedPatternInterface pat
      , Traversable (pat var)
      , SubstitutionClass s (Unified var) (Fix (pat var))
      , FreshVariablesClass m var
      , Ord (var Meta)
      , Ord (var Object)
      , Hashable var
      )
    => PatternSubstitutionClass s var pat m
  where
    substitute
        :: Fix (pat var)
        -> s (Unified var) (Fix (pat var))
        -> m (Fix (pat var))
    substitute p s = runReaderT (substituteM p) SubstitutionAndQuantifiedVars
        { substitution = s
        , quantifiedVars = freeVariables p
        }

substituteM
    :: PatternSubstitutionClass s var pat m
    => Fix (pat var)
    -> ReaderT
        (SubstitutionAndQuantifiedVars s (Unified var) (Fix (pat var)))
        m
        (Fix (pat var))
substituteM = patternTopDownVisitorM substitutePreprocess substituteVariable

substituteVariable
    :: (PatternSubstitutionClass s var pat m, MetaOrObject level)
    => Pattern level var (Fix (pat var))
    -> ReaderT
        (SubstitutionAndQuantifiedVars s (Unified var) (Fix (pat var)))
        m
        (Fix (pat var))
substituteVariable (VariablePattern v) = do
    subst <- asks substitution
    case lookup (asUnified v) subst of
        Just up -> return up
        Nothing -> return . Fix $ unifyPattern (VariablePattern v)
substituteVariable p = return . Fix $ unifyPattern p

{-
* if the substitution is empty, return the pattern unchanged;
* if the pattern is a binder, handle using 'binderPatternSubstitutePreprocess'
* if the pattern is not a binder recurse.
-}
substitutePreprocess
    :: (PatternSubstitutionClass s var pat m, MetaOrObject level)
    => Pattern level var (Fix (pat var))
    -> ReaderT (FixedSubstitutionAndQuantifiedVars s var pat)
        m
        (Either
            (Fix (pat var))
            ( Pattern level var (Fix (pat var))
            , ReaderT
                (FixedSubstitutionAndQuantifiedVars s var pat) m (Fix (pat var))
                -> ReaderT
                    (FixedSubstitutionAndQuantifiedVars s var pat)
                    m
                    (Fix (pat var))
            )
        )
substitutePreprocess p
  = do
    s <- ask
    if isEmpty s then return $ Left (Fix (unifyPattern p))
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
       , PatternSubstitutionClass s var pat m
       , MetaOrObject level)
    => FixedSubstitutionAndQuantifiedVars s var pat
    -> q level var (Fix (pat var))
    -> ReaderT (FixedSubstitutionAndQuantifiedVars s var pat)
        m (Either
            (Fix (pat var))
            ( Pattern level var (Fix (pat var))
            , ReaderT
                (FixedSubstitutionAndQuantifiedVars s var pat) m (Fix (pat var))
                -> ReaderT (FixedSubstitutionAndQuantifiedVars s var pat)
                    m (Fix (pat var))
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
            (insert unifiedVar (variableToPattern var'))
    | isJust (lookup unifiedVar s) =
        substituteFreeBinderBodyWith (delete unifiedVar)
    | otherwise = substituteFreeBinderBodyWith id
  where
    sort = getBinderPatternSort q
    var = getBinderPatternVariable q
    unifiedVar = asUnified var
    variableToPattern = Fix . unifyPattern . VariablePattern
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
