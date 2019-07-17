{-|
Module      : Kore.Variables.Free
Description : Specifies the 'TermWithVariablesClass' which is meant to define
              a term with variables and exports 'freeVariables'
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Variables.Free
    ( freePureVariables
    , freeSetVariables
    , pureAllVariables
    , synthetic
    , syntheticSet
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Control.Monad.Extra as Monad
import qualified Control.Monad.RWS.Strict as Monad.RWS
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import Kore.Syntax

-- | The free variables of a pure pattern.
freePureVariables
    :: Ord variable
    => Pattern variable annotation
    -> Set variable
freePureVariables root =
    let (free, ()) =
            Monad.RWS.execRWS
                (freePureVariables1 root)
                Set.empty  -- initial set of bound variables
                Set.empty  -- initial set of free variables
    in
        free
  where
    isBound v = Monad.RWS.asks (Set.member v)
    recordFree v = Monad.RWS.modify' (Set.insert v)

    freePureVariables1 recursive =
        case Cofree.tailF (Recursive.project recursive) of
            VariableF v -> Monad.unlessM (isBound v) (recordFree v)
            ExistsF Exists { existsVariable, existsChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert existsVariable)
                    -- descend into the bound pattern
                    (freePureVariables1 existsChild)
            ForallF Forall { forallVariable, forallChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert forallVariable)
                    -- descend into the bound pattern
                    (freePureVariables1 forallChild)
            p -> mapM_ freePureVariables1 p

-- | The free set variables of a pure pattern.
freeSetVariables
    :: forall variable annotation
     . Ord variable
    => Pattern variable annotation
    -> Set variable
freeSetVariables root =
    let (free, ()) =
            Monad.RWS.execRWS
                (freeSetVariables1 root)
                Set.empty  -- initial set of bound variables
                Set.empty  -- initial set of free variables
    in
        free
  where
    isBound v = Monad.RWS.asks (Set.member v)
    recordFree v = Monad.RWS.modify' (Set.insert v)

    freeSetVariables1 recursive =
        case Cofree.tailF (Recursive.project recursive) of
            SetVariableF (SetVariable v) -> Monad.unlessM (isBound v) (recordFree v)
            MuF Mu { muVariable = SetVariable v, muChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert v)
                    -- descend into the bound pattern
                    (freeSetVariables1 muChild)
            NuF Nu { nuVariable = SetVariable v, nuChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert v)
                    -- descend into the bound pattern
                    (freeSetVariables1 nuChild)
            p -> mapM_ freeSetVariables1 p

pureMergeVariables
    :: Ord variable
    => Base
        (Pattern variable annotation)
        (Set.Set variable)
    -> Set.Set variable
pureMergeVariables base =
    case Cofree.tailF base of
        VariableF v -> Set.singleton v
        ExistsF Exists { existsVariable, existsChild } ->
            Set.insert existsVariable existsChild
        ForallF Forall { forallVariable, forallChild } ->
            Set.insert forallVariable forallChild
        p -> Foldable.foldl' Set.union Set.empty p

{-| 'pureAllVariables' extracts all variables of a given level in a pattern as a
set, regardless of whether they are quantified or not.
-}
pureAllVariables
    :: Ord variable
    => Pattern variable annotation
    -> Set.Set variable
pureAllVariables = Recursive.fold pureMergeVariables

{- | @synthetic@ is an algebra for the free variables of a pattern.

Use @synthetic@ with 'Kore.Annotation.synthesize' to annotate a pattern with its
free variables as a synthetic attribute.

 -}
synthetic
    :: Ord variable
    => PatternF variable (Set.Set variable)
    -> Set.Set variable
synthetic (ExistsF Exists { existsVariable, existsChild }) =
    Set.delete existsVariable existsChild
synthetic (ForallF Forall { forallVariable, forallChild }) =
    Set.delete forallVariable forallChild
synthetic (VariableF variable) =
    Set.singleton variable
synthetic patternHead =
    Foldable.foldl' Set.union Set.empty patternHead
{-# INLINE synthetic #-}

{- | @syntheticSet@ is an algebra for the free set variables of a pattern.

Use @syntheticSet@ with 'Kore.Annotation.synthesize' to annotate a pattern with its
free variables as a synthetic attribute.

 -}
syntheticSet
    :: Ord variable
    => PatternF variable (Set.Set variable)
    -> Set.Set variable
syntheticSet (MuF Mu { muVariable = SetVariable v, muChild }) =
    Set.delete v muChild
syntheticSet (NuF Nu { nuVariable = SetVariable v, nuChild }) =
    Set.delete v nuChild
syntheticSet (SetVariableF (SetVariable variable)) =
    Set.singleton variable
syntheticSet patternHead =
    Foldable.foldl' Set.union Set.empty patternHead
{-# INLINE syntheticSet #-}
