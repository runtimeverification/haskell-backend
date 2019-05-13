{-|
Module      : Kore.Substitute
Description : Abstract substitution algorithm
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module Kore.Substitute
    ( substitute
    -- * Binders
    , Binder (..)
    , existsBinder
    , forallBinder
    ) where

import           Control.Applicative
import qualified Control.Lens as Lens
import qualified Control.Monad.Except as Monad.Except
import           Control.Monad.Trans.Maybe
import qualified Data.Foldable as Foldable
import           Data.Functor.Foldable
                 ( Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import Kore.Syntax
import Kore.Variables.Fresh

data Binder variable child =
    Binder { binderVariable :: !variable, binderChild :: !child }

-- | A 'Lens.Lens' to view an 'Exists' as a 'Binder'.
existsBinder :: Lens.Lens' (Exists sort variable child) (Binder variable child)
existsBinder mapping exists =
    finish <$> mapping binder
  where
    binder =
        Binder { binderVariable, binderChild }
      where
        Exists { existsVariable = binderVariable } = exists
        Exists { existsChild    = binderChild    } = exists
    finish binder' =
        exists { existsVariable, existsChild }
      where
        Binder { binderVariable = existsVariable } = binder'
        Binder { binderChild    = existsChild    } = binder'

-- | A 'Lens.Lens' to view a 'Forall' as a 'Binder'.
forallBinder :: Lens.Lens' (Forall sort variable child) (Binder variable child)
forallBinder mapping forall =
    finish <$> mapping binder
  where
    binder =
        Binder { binderVariable, binderChild }
      where
        Forall { forallVariable = binderVariable } = forall
        Forall { forallChild    = binderChild    } = forall
    finish binder' =
        forall { forallVariable, forallChild }
      where
        Binder { binderVariable = forallVariable } = binder'
        Binder { binderChild    = forallChild    } = binder'

{- | Traverse the pattern from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

The substitution must be normalized, i.e. no target (left-hand side) variable
may appear in the right-hand side of any substitution, but this is not checked.

 -}
-- TODO (thomas.tuegel): In the future, patterns may have other types of
-- attributes which need to be re-synthesized after substitution.
substitute
    ::  forall patternType patternBase attribute variable.
        ( FreshVariable variable
        , Ord variable
        , SortedVariable variable
        , Corecursive patternType, Recursive patternType
        , Functor patternBase
        , CofreeF patternBase attribute ~ Base patternType
        )
    => Lens.Lens' patternType (Set variable)
    -- ^ Lens into free variables of the pattern
    ->  (   forall f
        .   Alternative f
        =>  (Binder variable patternType -> f (Binder variable patternType))
        ->  patternType -> f patternType
        )
    -- ^ Match a 'Binder' in @patternType.
    ->  (   forall f
        .   Alternative f
        =>  (variable -> f variable)
        ->  patternType -> f patternType
        )
    -- ^ Match a @variable@ in @patternType.
    -> Map variable patternType
    -- ^ Substitution
    -> patternType
    -- ^ Original pattern
    -> patternType
substitute lensFreeVariables matchBinder matchVariable =
    \subst -> substituteWorker (Map.map Left subst)
  where
    extractFreeVariables :: patternType -> Set variable
    extractFreeVariables = Lens.view lensFreeVariables

    -- | Insert a variable renaming into the substitution.
    renaming
        :: variable  -- ^ Original variable
        -> variable  -- ^ Renamed variable
        -> Map variable (Either patternType variable)  -- ^ Substitution
        -> Map variable (Either patternType variable)
    renaming variable variable' = Map.insert variable (Right variable')

    substituteWorker
        :: Map variable (Either patternType variable)
        -> patternType
        -> patternType
    substituteWorker subst termLike
      | Map.null subst' =
        -- If there are no targeted free variables, return the original pattern.
        -- Note that this covers the case of a non-targeted variable pattern,
        -- which produces an error below.
        termLike

      | Just termLike' <- matchBinder underBinder termLike = termLike'

      | Just termLike' <- matchEither (matchVariable overVariable termLike) =
        termLike'

      | otherwise =
        -- All other patterns
        let termLikeHead' = substituteWorker subst' <$> termLikeHead
        in embed termLikeHead'
      where
        attrib :< termLikeHead = Recursive.project termLike
        freeVariables = extractFreeVariables termLike
        embed =
            Lens.set lensFreeVariables freeVariables'
            . Recursive.embed
            . (attrib :<)
        -- | The substitution applied to subterms, including only the free
        -- variables below the current node. Shadowed variables are
        -- automatically omitted.
        subst' = Map.intersection subst (Map.fromSet id freeVariables)
        -- | Free variables of the original pattern that are not targeted.
        originalVariables = Set.difference freeVariables (Map.keysSet subst')
        -- | Free variables of the resulting pattern.
        freeVariables' = Set.union originalVariables targetFreeVariables
          where
            -- | Free variables of the target substitutions.
            targetFreeVariables =
                Foldable.foldl' Set.union Set.empty
                    (either extractFreeVariables Set.singleton <$> subst')
        -- | Rename a bound variable, if needed.
        avoidCapture = refreshVariable freeVariables'

        underBinder binder = do
            let Binder { binderVariable } = binder
            binderVariable' <- avoidCapture binderVariable
            -- Rename the freshened bound variable in the subterms.
            let subst'' = renaming binderVariable binderVariable' subst'
                Binder { binderChild } = binder
            return Binder
                { binderVariable = binderVariable'
                , binderChild = substituteWorker subst'' binderChild
                }

        overVariable :: variable -> MaybeT (Either patternType) variable
        overVariable variable = do
            case Map.lookup variable subst' of
                Nothing ->
                    -- This is impossible: if the pattern is a non-targeted
                    -- variable, we would have taken the first branch at
                    -- the top of substituteWorker.
                    error "Internal error: Impossible free variable"
                Just (Right variable')  -> return variable'
                Just (Left termLike')   -> Monad.Except.throwError termLike'

        matchEither :: MaybeT (Either r) r -> Maybe r
        matchEither = fmap (either id id) . sequence . runMaybeT

{-# INLINE substitute #-}
