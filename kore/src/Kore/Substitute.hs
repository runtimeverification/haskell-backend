{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Substitute
    ( substitute
    ) where

import Prelude.Kore

import Data.Functor.Foldable
    ( Corecursive
    , Recursive
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Functor.Identity ( Identity(runIdentity) )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set

import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Synthetic
import Kore.Internal.Variable
import Kore.Syntax
import Kore.Variables.Binding
import Kore.Variables.Fresh

{- | Traverse the pattern from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

The substitution must be normalized, i.e. no target (left-hand side) variable
may appear in the right-hand side of any substitution, but this is not checked.

 -}
substitute
    ::  forall patternType patternBase attribute variable.
        ( InternalVariable variable
        , Corecursive patternType, Recursive patternType
        , CofreeF patternBase attribute ~ Base patternType
        , Binding patternType
        , VariableType patternType ~ variable
        , Synthetic attribute patternBase
        , HasFreeVariables patternType variable
        )
    => Map (SomeVariableName variable) patternType
    -- ^ Substitution
    -> patternType
    -- ^ Original pattern
    -> patternType
substitute =
    substituteWorker . Map.map Left
  where
    extractFreeVariables :: patternType -> Set (SomeVariableName variable)
    extractFreeVariables = FreeVariables.toNames . freeVariables

    getTargetFreeVariables
        :: Either patternType (SomeVariable variable)
        -> Set (SomeVariableName variable)
    getTargetFreeVariables =
        either extractFreeVariables (Set.singleton . variableName)

    -- | Insert an optional variable renaming into the substitution.
    renaming
        :: SomeVariable variable  -- ^ Original variable
        -> Maybe (SomeVariable variable)  -- ^ Renamed variable
        -> Map
            (SomeVariableName variable)
            (Either patternType (SomeVariable variable))
        -- ^ Substitution
        -> Map
            (SomeVariableName variable)
            (Either patternType (SomeVariable variable))
    renaming Variable { variableName } =
        maybe id (Map.insert variableName . Right)

    substituteWorker
        :: Map
            (SomeVariableName variable)
            (Either patternType (SomeVariable variable))
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
                :: Binder (SomeVariable variable) patternType
                -> Identity (Binder (SomeVariable variable) patternType)
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
            worker
                :: SomeVariable variable
                -> Either patternType (SomeVariable variable)
            worker Variable { variableName } =
                -- If the variable is not substituted or renamed, return the
                -- original pattern.
                fromMaybe
                    (Left termLike)
                    -- If the variable is renamed, 'Map.lookup' returns a
                    -- 'Right' which @traverseVariable@ embeds into
                    -- @patternType@. If the variable is substituted,
                    -- 'Map.lookup' returns a 'Left' which is used directly as
                    -- the result, exiting early from @traverseVariable@.
                    (Map.lookup variableName subst')

        -- | Default case: Descend into sub-patterns and apply the substitution.
        substituteDefault =
            synthesize termLikeHead'
          where
            _ :< termLikeHead = Recursive.project termLike
            termLikeHead' = substituteWorker subst' <$> termLikeHead

        freeVars = extractFreeVariables termLike

        -- | The substitution applied to subterms, including only the free
        -- variables below the current node. Shadowed variables are
        -- automatically omitted.
        subst' = Map.intersection subst (Map.fromSet id freeVars)

        -- | Free variables of the original pattern that are not targeted.
        originalVariables = Set.difference freeVars (Map.keysSet subst')

        -- | Free variables of the resulting pattern.
        freeVariables' = Set.union originalVariables targetFreeVariables
          where
            -- | Free variables of the target substitutions.
            targetFreeVariables =
                foldl' Set.union Set.empty
                    (getTargetFreeVariables <$> subst')

        -- | Rename a bound variable, if needed.
        avoidCapture = refreshVariable freeVariables'

{-# INLINE substitute #-}
