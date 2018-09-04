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
variables than its terms can.  'freeVars' is used to track the free
variables in a substitution context.
-}
data SubstitutionAndQuantifiedVars s var pat = SubstitutionAndQuantifiedVars
    { substitution   :: s var pat
    , freeVars :: Set.Set var
    }

type FixedSubstitutionAndQuantifiedVars s var pat =
    SubstitutionAndQuantifiedVars s (Unified var) (Fix (pat domain var))

addFreeVariable
    :: (Ord var)
    => var
    -> SubstitutionAndQuantifiedVars s var pat
    -> SubstitutionAndQuantifiedVars s var pat
addFreeVariable v s = s { freeVars = v `Set.insert` freeVars s }

instance (SubstitutionClass s var pat)
    => MapClass (SubstitutionAndQuantifiedVars s) var pat
  where
    isEmpty = isEmpty . substitution
    empty = SubstitutionAndQuantifiedVars
        { substitution = empty
        , freeVars = Set.empty
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
      , Traversable (pat domain var)
      , SubstitutionClass s (Unified var) (Fix (pat domain var))
      , FreshVariablesClass m var
      , Ord (var Meta)
      , Ord (var Object)
      , Hashable var
      )
    => PatternSubstitutionClass s var pat m
  where
    substitute
        :: Fix (pat domain var)
        -> s (Unified var) (Fix (pat domain var))
        -> m (Fix (pat domain var))
    substitute p s = substituteM (SubstitutionAndQuantifiedVars
        { substitution = s
        , freeVars = freeVariables p
        }) p

substituteM
    :: forall s var pat m .
       PatternSubstitutionClass s var pat m
    => SubstitutionAndQuantifiedVars s (Unified var) (Fix (pat domain var))
    -> Fix (pat domain var)
    -> m (Fix (pat domain var))
substituteM subst p | isEmpty subst = return p
substituteM subst p = unifiedPatternApply @pat substPattern  (project p)
  where
    substPattern :: (MetaOrObject level')
                 => Pattern level domain' var (Fix (pat domain var))
                 -> m (Fix (pat domain var))
    substPattern (ExistsPattern e)  = binderPatternSubstitutePreprocess subst e
    substPattern (ForallPattern f) = binderPatternSubstitutePreprocess subst f
    substPattern domain varPat@(VariablePattern domain v) = do
        return $ case lookup (asUnified v) subst of
                     Just up -> up
                     Nothing -> Fix (unifyPattern domain varPat)
    substPattern otherPat = fmap (Fix . unifyPattern) (mapM (substituteM subst) otherPat)

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
    -> q level var (Fix (pat domain var))
    -> m (Fix (pat domain var))
binderPatternSubstitutePreprocess s q
    | unifiedVar `Set.member` substitutionFreeVars
      = do
        var' <- freshVariableSuchThat
            var
            ( not
            . (`Set.member` allFreeVars)
            . asUnified
            )
        let s' = insert unifiedVar (toPat $ VariablePattern domain var') s
        pat' <- substituteM s' pat
        return $ toPat $
            binderPatternConstructor q sort var' pat'
    | otherwise = do
          let s' = addFreeVariable unifiedVar $
                   if isJust (lookup unifiedVar s)
                   then delete unifiedVar s else s
          pat' <- substituteM s' pat
          return $ toPat $
            binderPatternConstructor q sort var pat'
  where
    toPat p = Fix (unifyPattern p)
    (sort,var,pat) = (getBinderPatternSort q
                     ,getBinderPatternVariable q
                     ,getBinderPatternChild q)
    unifiedVar = asUnified var
    substitutionFreeVars = substitutionTermsFreeVars (delete unifiedVar s)
    allFreeVars = substitutionFreeVars `Set.union` freeVars s
