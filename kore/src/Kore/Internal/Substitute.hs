{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Internal.Substitute (
    Substitute (..),
    rename,
) where

import qualified Data.Functor.Foldable as Recursive
import Data.Functor.Identity
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables (freeVariables),
 )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Attribute.Synthetic (
    synthesize,
 )
import Kore.Internal.TermLike.TermLike (
    TermLike,
    mkVar,
 )
import Kore.Internal.Variable
import Kore.Variables.Binding
import Kore.Variables.Fresh (
    refreshVariable,
 )
import Prelude.Kore

class
    (InternalVariable variable, HasFreeVariables child variable) =>
    Substitute variable child
        | child -> variable
    where
    substitute ::
        Map (SomeVariableName variable) (TermLike variable) ->
        child ->
        child

rename ::
    Substitute variable child =>
    Map (SomeVariableName variable) (SomeVariable variable) ->
    child ->
    child
rename = substitute . fmap mkVar
{-# INLINE rename #-}

instance
    InternalVariable variable =>
    Substitute variable (TermLike variable)
    where
    substitute = substituteWorker . Map.map Left
      where
        extractFreeVariables ::
            TermLike variable -> Set (SomeVariableName variable)
        extractFreeVariables = FreeVariables.toNames . freeVariables

        getTargetFreeVariables ::
            Either (TermLike variable) (SomeVariable variable) ->
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
                (Either (TermLike variable) (SomeVariable variable)) ->
            Map
                (SomeVariableName variable)
                (Either (TermLike variable) (SomeVariable variable))
        renaming Variable{variableName} =
            maybe id (Map.insert variableName . Right)

        substituteWorker ::
            Map
                (SomeVariableName variable)
                (Either (TermLike variable) (SomeVariable variable)) ->
            TermLike variable ->
            TermLike variable
        substituteWorker subst termLike =
            substituteNone <|> substituteBinder <|> substituteVariable
                & fromMaybe substituteDefault
          where
            substituteNone :: Maybe (TermLike variable)
            substituteNone
                | Map.null subst' = pure termLike
                | otherwise = empty

            substituteBinder :: Maybe (TermLike variable)
            substituteBinder =
                runIdentity <$> matchWith traverseBinder worker termLike
              where
                worker ::
                    Binder (SomeVariable variable) (TermLike variable) ->
                    Identity (Binder (SomeVariable variable) (TermLike variable))
                worker Binder{binderVariable, binderChild} = do
                    let binderVariable' = avoidCapture binderVariable
                        -- Rename the freshened bound variable in the subterms.
                        subst'' = renaming binderVariable binderVariable' subst'
                    return
                        Binder
                            { binderVariable = fromMaybe binderVariable binderVariable'
                            , binderChild = substituteWorker subst'' binderChild
                            }

            substituteVariable :: Maybe (TermLike variable)
            substituteVariable =
                either id id <$> matchWith traverseVariable worker termLike
              where
                worker ::
                    SomeVariable variable ->
                    Either (TermLike variable) (SomeVariable variable)
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
