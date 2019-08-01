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
import Kore.Variables.UnifiedVariable
       ( UnifiedVariable (..) )

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
                Monad.unlessM (isBound (ElemVar v)) (recordFree (ElemVar v))
            ExistsF Exists { existsVariable, existsChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (ElemVar existsVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 existsChild)
            ForallF Forall { forallVariable, forallChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (ElemVar forallVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 forallChild)
            SetVariableF (SetVariable v) ->
                Monad.unlessM (isBound (SetVar v)) (recordFree (SetVar v))
            MuF Mu { muVariable = SetVariable v, muChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (SetVar v))
                    -- descend into the bound pattern
                    (freePureVariables1 muChild)
            NuF Nu { nuVariable = SetVariable v, nuChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (SetVar v))
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
        VariableF v -> Set.singleton (ElemVar v)
        ExistsF Exists { existsVariable, existsChild } ->
            Set.insert (ElemVar existsVariable) existsChild
        ForallF Forall { forallVariable, forallChild } ->
            Set.insert (ElemVar forallVariable) forallChild
        SetVariableF (SetVariable v) -> Set.singleton (SetVar v)
        MuF Mu { muVariable = SetVariable muVar, muChild } ->
            Set.insert (SetVar muVar) muChild
        NuF Nu { nuVariable = SetVariable nuVar, nuChild } ->
            Set.insert (SetVar nuVar) nuChild
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
    Set.delete (ElemVar existsVariable) existsChild
synthetic (ForallF Forall { forallVariable, forallChild }) =
    Set.delete (ElemVar forallVariable) forallChild
synthetic (VariableF variable) =
    Set.singleton (ElemVar variable)
synthetic (MuF Mu { muVariable = SetVariable muVar, muChild }) =
    Set.delete (SetVar muVar) muChild
synthetic (NuF Nu { nuVariable = SetVariable nuVar, nuChild }) =
    Set.delete (SetVar nuVar) nuChild
synthetic (SetVariableF (SetVariable variable)) =
    Set.singleton (SetVar variable)
synthetic patternHead =
    Foldable.foldl' Set.union Set.empty patternHead
{-# INLINE synthetic #-}

{- | @syntheticSet@ is an algebra for the free set variables of a pattern.

Use @syntheticSet@ with 'Kore.Annotation.synthesize' to annotate a pattern with
its free variables as a synthetic attribute.

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
