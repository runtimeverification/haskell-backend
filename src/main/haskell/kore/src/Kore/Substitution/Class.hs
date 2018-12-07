{-|
Module      : Kore.Substitution.Class
Description : Defines basic interfaces and main functionality needed
              to implement substitution for an 'UnifiedPatternInterface'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Substitution.Class
    ( SubstitutionClass (..)
    , substitute
    ) where

import           Control.Comonad
import           Data.Functor.Foldable
                 ( Base, Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive
import           Data.Maybe
                 ( isJust )
import qualified Data.Set as Set
import           Prelude hiding
                 ( lookup )

import Data.Map.Class
import Kore.AST.MLPatterns
import Kore.AST.Pure
import Kore.Variables.Free
import Kore.Variables.Fresh

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
    { substitution :: s var pat
    , freeVars :: Set.Set var
    }

type FixedSubstitutionAndQuantifiedVars s var t =
    SubstitutionAndQuantifiedVars s (Unified var) t

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

-- | Apply a substitution @s@ to a pattern @pat@.
substitute
    ::  ( UnifiedPatternInterface pat
        , SubstitutionClass subst (Unified var) (f ann)
        , MonadCounter m
        , Traversable dom
        , OrdMetaOrObject var
        , FreshVariable var
        , Corecursive (f ann)
        , Recursive (f ann)
        , Base (f ann) ~ CofreeF (pat dom var) ann
        , Comonad f
        )
    => f ann
    -> subst (Unified var) (f ann)
    -> m (f ann)
substitute p s =
    substituteM
        SubstitutionAndQuantifiedVars
            { substitution = s
            , freeVars = freeVariables p
            }
        p

substituteM
    ::  forall subst pat (dom :: * -> *) var m f ann.
        ( MonadCounter m
        , SubstitutionClass subst (Unified var) (f ann)
        , UnifiedPatternInterface pat
        , Traversable dom
        , FreshVariable var
        , OrdMetaOrObject var
        , Recursive (f ann), Corecursive (f ann)
        , Base (f ann) ~ CofreeF (pat dom var) ann
        , Comonad f
        )
    => SubstitutionAndQuantifiedVars subst (Unified var) (f ann)
    -> f ann
    -> m (f ann)
substituteM subst p
  | isEmpty subst = return p
  | otherwise =
    case Recursive.project p of
        ann :< projected ->
            unifiedPatternApply (substPattern ann) projected
  where
    substPattern
        :: MetaOrObject level'
        => ann
        -> Pattern level' dom var (f ann)
        -> m (f ann)
    substPattern ann =
        \case
            ExistsPattern e ->
                binderPatternSubstitutePreprocess subst ann e
            ForallPattern f ->
                binderPatternSubstitutePreprocess subst ann f
            var@(VariablePattern v) ->
                return $ case lookup (asUnified v) subst of
                    Just up -> ann <$ up
                    Nothing -> Recursive.embed (ann :< unifyPattern var)
            other ->
                (<$>)
                    (Recursive.embed . (:<) ann . unifyPattern)
                    (mapM (substituteM subst) other)

{-
* if the quantified variable is among the encountered free variables
  in this contex, add an alpha-renaming binding to the substitution
* if the quantified variable is replaced by this substitution,
  susbtitute the body using the substitution without this variable
* otherwise, do a full substitution of the body (remembering that, in this
  context, the quantified variable is free).
-}
binderPatternSubstitutePreprocess
    ::  forall subst level binder pat (dom :: * -> *) (var :: * -> *) ann m f.
        ( MLBinderPatternClass binder
        , MetaOrObject level
        , MonadCounter m
        , SubstitutionClass subst (Unified var) (f ann)
        , FreshVariable var
        , UnifiedPatternInterface pat
        , Traversable dom
        , OrdMetaOrObject var
        , Corecursive (f ann)
        , Recursive (f ann)
        , Base (f ann) ~ CofreeF (pat dom var) ann
        , Comonad f
        )
    => FixedSubstitutionAndQuantifiedVars subst var (f ann)
    -> ann
    -> binder level var (f ann)
    -> m (f ann)
binderPatternSubstitutePreprocess s ann q
    | unifiedVar `Set.member` substitutionFreeVars
      = do
        var' <- freshVariableSuchThat
            var
            ( not
            . (`Set.member` allFreeVars)
            . asUnified
            )
        let s' = insert unifiedVar (toPat $ VariablePattern var') s
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
    toPat p = Recursive.embed (ann :< unifyPattern p)
    (sort,var,pat) = (getBinderPatternSort q
                     ,getBinderPatternVariable q
                     ,getBinderPatternChild q)
    unifiedVar = asUnified var
    substitutionFreeVars = substitutionTermsFreeVars (delete unifiedVar s)
    allFreeVars = substitutionFreeVars `Set.union` freeVars s
