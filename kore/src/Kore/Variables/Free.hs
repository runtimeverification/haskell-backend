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
    , pureAllVariables
    , synthetic
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
import Kore.Variables.UnifiedVariable

-- | The free variables of a pure pattern.
freePureVariables
    :: Ord variable
    => Pattern variable annotation
    -> Set (UnifiedVariable variable)
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
            VariableF v ->
                Monad.unlessM (isBound v) (recordFree v)
            ExistsF Exists { existsVariable, existsChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (asUnifiedVariable existsVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 existsChild)
            ForallF Forall { forallVariable, forallChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (asUnifiedVariable forallVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 forallChild)
            MuF Mu { muVariable, muChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (asUnifiedVariable muVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 muChild)
            NuF Nu { nuVariable, nuChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (asUnifiedVariable nuVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 nuChild)
            p -> mapM_ freePureVariables1 p

pureMergeVariables
    :: Ord variable
    => Base
        (Pattern variable annotation)
        (Set.Set (UnifiedVariable variable))
    -> Set.Set (UnifiedVariable variable)
pureMergeVariables base =
    case Cofree.tailF base of
        VariableF v -> Set.singleton v
        ExistsF Exists { existsVariable, existsChild } ->
            Set.insert (asUnifiedVariable existsVariable) existsChild
        ForallF Forall { forallVariable, forallChild } ->
            Set.insert (asUnifiedVariable forallVariable) forallChild
        MuF Mu { muVariable, muChild } ->
            Set.insert (asUnifiedVariable muVariable) muChild
        NuF Nu { nuVariable, nuChild } ->
            Set.insert (asUnifiedVariable nuVariable) nuChild
        p -> Foldable.foldl' Set.union Set.empty p

{-| 'pureAllVariables' extracts all variables of a given level in a pattern as a
set, regardless of whether they are quantified or not.
-}
pureAllVariables
    :: Ord variable
    => Pattern variable annotation
    -> Set.Set (UnifiedVariable variable)
pureAllVariables = Recursive.fold pureMergeVariables

{- | @synthetic@ is an algebra for the free variables of a pattern.

Use @synthetic@ with 'Kore.Annotation.synthesize' to annotate a pattern with its
free variables as a synthetic attribute.

 -}
synthetic
    :: Ord variable
    => PatternF variable (Set.Set (UnifiedVariable variable))
    -> Set.Set (UnifiedVariable variable)
synthetic (ExistsF Exists { existsVariable, existsChild }) =
    Set.delete (asUnifiedVariable existsVariable) existsChild
synthetic (ForallF Forall { forallVariable, forallChild }) =
    Set.delete (asUnifiedVariable forallVariable) forallChild
synthetic (VariableF variable) = Set.singleton variable
synthetic (MuF Mu { muVariable, muChild }) =
    Set.delete (asUnifiedVariable muVariable) muChild
synthetic (NuF Nu { nuVariable, nuChild }) =
    Set.delete (asUnifiedVariable nuVariable) nuChild
synthetic patternHead =
    Foldable.foldl' Set.union Set.empty patternHead
{-# INLINE synthetic #-}
