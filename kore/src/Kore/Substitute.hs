{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Substitute (
    substitute,
) where

import Data.Functor.Foldable (
    Corecursive,
    Recursive,
 )
import qualified Data.Functor.Foldable as Recursive
import Data.Functor.Identity (
    Identity (runIdentity),
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables (..),
 )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Synthetic
import Kore.Internal.Variable
import Kore.Syntax
import Kore.Variables.Binding
import Kore.Variables.Fresh
import Prelude.Kore

{- | Traverse the pattern from the top down and apply substitutions.

The 'freeVariables' annotation is used to avoid traversing subterms that
contain none of the targeted variables.

The substitution must be normalized, i.e. no target (left-hand side) variable
may appear in the right-hand side of any substitution, but this is not checked.
-}
substitute ::
    forall patternType patternBase attribute variable.
    ( InternalVariable variable
    , Corecursive patternType
    , Recursive patternType
    , CofreeF patternBase attribute ~ Base patternType
    , Binding patternType
    , VariableType patternType ~ variable
    , Synthetic attribute patternBase
    , HasFreeVariables patternType variable
    ) =>
    -- | Substitution
    Map (SomeVariableName variable) patternType ->
    -- | Original pattern
    patternType ->
    patternType
substitute =
    substituteWorker . Map.map Left
  where
    extractFreeVariables :: patternType -> Set (SomeVariableName variable)
    extractFreeVariables = FreeVariables.toNames . freeVariables

    getTargetFreeVariables ::
        Either patternType (SomeVariable variable) ->
        Set (SomeVariableName variable)
    getTargetFreeVariables =
        either extractFreeVariables (Set.singleton . variableName)

    renaming ::
        -- | Original variable
        SomeVariable variable ->
        -- | Renamed variable
        Maybe (SomeVariable variable) ->
        -- | Substitution
        Map
            (SomeVariableName variable)
            (Either patternType (SomeVariable variable)) ->
        Map
            (SomeVariableName variable)
            (Either patternType (SomeVariable variable))
    renaming Variable{variableName} =
        maybe id (Map.insert variableName . Right)

    substituteWorker ::
        Map
            (SomeVariableName variable)
            (Either patternType (SomeVariable variable)) ->
        patternType ->
        patternType
    substituteWorker subst termLike =
        substituteNone <|> substituteBinder <|> substituteVariable
            & fromMaybe substituteDefault
      where
        substituteNone :: Maybe patternType
        substituteNone
            | Map.null subst' = pure termLike
            | otherwise = empty

        substituteBinder :: Maybe patternType
        substituteBinder =
            runIdentity <$> matchWith traverseBinder worker termLike
          where
            worker ::
                Binder (SomeVariable variable) patternType ->
                Identity (Binder (SomeVariable variable) patternType)
            worker Binder{binderVariable, binderChild} = do
                let binderVariable' = avoidCapture binderVariable
                    -- Rename the freshened bound variable in the subterms.
                    subst'' = renaming binderVariable binderVariable' subst'
                return
                    Binder
                        { binderVariable = fromMaybe binderVariable binderVariable'
                        , binderChild = substituteWorker subst'' binderChild
                        }

        substituteVariable :: Maybe patternType
        substituteVariable =
            either id id <$> matchWith traverseVariable worker termLike
          where
            worker ::
                SomeVariable variable ->
                Either patternType (SomeVariable variable)
            worker Variable{variableName} =
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

        substituteDefault =
            synthesize termLikeHead'
          where
            _ :< termLikeHead = Recursive.project termLike
            termLikeHead' = substituteWorker subst' <$> termLikeHead

        freeVars = extractFreeVariables termLike

        subst' = Map.intersection subst (Map.fromSet id freeVars)

        originalVariables = Set.difference freeVars (Map.keysSet subst')

        freeVariables' = Set.union originalVariables targetFreeVariables
          where
            targetFreeVariables =
                foldl'
                    Set.union
                    Set.empty
                    (getTargetFreeVariables <$> subst')

        avoidCapture = refreshVariable freeVariables'
{-# INLINE substitute #-}
