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
import           Control.Comonad.Trans.Env
import qualified Control.Lens as Lens
import qualified Data.Foldable as Foldable
import           Data.Function
                 ( (&) )
import           Data.Functor.Foldable
                 ( Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive
import           Data.Functor.Identity
import           Data.Map.Strict
                 ( Map )
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Monoid
                 ( Any (..) )
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
        .   Applicative f
        =>  (Binder variable patternType -> f (Binder variable patternType))
        ->  patternType -> f patternType
        )
    -- ^ Traverse a 'Binder' in @patternType@.
    ->  (   forall f
        .   Applicative f
        =>  (variable -> f variable)
        ->  patternType -> f patternType
        )
    -- ^ Traverse a @variable@ in @patternType@.
    -> Map variable patternType
    -- ^ Substitution
    -> patternType
    -- ^ Original pattern
    -> patternType
substitute lensFreeVariables traverseBinder traverseVariable =
    \subst -> substituteWorker (Map.map Left subst)
  where
    extractFreeVariables :: patternType -> Set variable
    extractFreeVariables = Lens.view lensFreeVariables

    -- | Insert an optional variable renaming into the substitution.
    renaming
        :: variable  -- ^ Original variable
        -> Maybe variable  -- ^ Renamed variable
        -> Map variable (Either patternType variable)  -- ^ Substitution
        -> Map variable (Either patternType variable)
    renaming variable = maybe id (Map.insert variable . Right)

    substituteWorker
        :: Map variable (Either patternType variable)
        -> patternType
        -> patternType
    substituteWorker subst termLike =
        substituteNone <|> substituteBinder <|> substituteVariable
        & fromMaybe substituteDefault
      where
        -- | Special case: None of the targeted variables occurs in the pattern.
        -- There is nothing to substitute, return the original pattern.
        substituteNone :: Maybe patternType
        substituteNone
          | Map.null subst' = pure termLike
          | otherwise       = empty

        -- | Special case: The pattern is a binder.
        -- The bound variable may be renamed to avoid capturing free variables
        -- in the substitutions. The substitution (and renaming, if necessary)
        -- is carried out on the bound pattern.
        substituteBinder :: Maybe patternType
        substituteBinder =
            runIdentity <$> matchWith traverseBinder worker termLike
          where
            worker
                :: Binder variable patternType
                -> Identity (Binder variable patternType)
            worker Binder { binderVariable, binderChild } = do
                let
                    binderVariable' = avoidCapture binderVariable
                    -- Rename the freshened bound variable in the subterms.
                    subst'' = renaming binderVariable binderVariable' subst'
                return Binder
                    { binderVariable = fromMaybe binderVariable binderVariable'
                    , binderChild = substituteWorker subst'' binderChild
                    }

        -- | Special case: The pattern is a variable.
        -- Substitute or rename the variable, as required.
        substituteVariable :: Maybe patternType
        substituteVariable =
            either id id <$> matchWith traverseVariable worker termLike
          where
            worker :: variable -> Either patternType variable
            worker variable =
                -- If the variable is not substituted or renamed, return the
                -- original pattern.
                fromMaybe
                    (Left termLike)
                    -- If the variable is renamed, 'Map.lookup' returns a
                    -- 'Right' which @traverseVariable@ embeds into
                    -- @patternType@. If the variable is substituted,
                    -- 'Map.lookup' returns a 'Left' which is used directly as
                    -- the result, exiting early from @traverseVariable@.
                    (Map.lookup variable subst')

        -- | Default case: Descend into sub-patterns and apply the substitution.
        substituteDefault =
            embed termLikeHead'
          where
            attrib :< termLikeHead = Recursive.project termLike
            termLikeHead' = substituteWorker subst' <$> termLikeHead
            embed =
                Lens.set lensFreeVariables freeVariables'
                . Recursive.embed
                . (attrib :<)

        freeVariables = extractFreeVariables termLike

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

{-# INLINE substitute #-}

matchWith
    :: Applicative f
    => (forall f'. Applicative f' => (a -> f' b) -> s -> f' t)  -- ^ Traversal
    -> (a -> f b)
    -> s -> Maybe (f t)
matchWith traverse' afb s =
    let (getAny -> matched, ft) = runEnvT (traverse' (EnvT (Any True) . afb) s)
    in if matched then Just ft else Nothing
