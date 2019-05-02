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
import qualified Control.Monad as Monad
import qualified Control.Monad.RWS.Strict as Monad.RWS
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import Kore.Syntax

-- | The free variables of a pure pattern.
freePureVariables
    :: (Foldable domain, Functor domain, Ord variable)
    => PurePattern domain variable annotation
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
    unlessM m go = m >>= \b -> Monad.unless b go
    isBound v = Monad.RWS.asks (Set.member v)
    recordFree v = Monad.RWS.modify' (Set.insert v)

    freePureVariables1 recursive =
        case Cofree.tailF (Recursive.project recursive) of
            VariableF v -> unlessM (isBound v) (recordFree v)
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

pureMergeVariables
    :: (Foldable domain, Ord variable)
    => Base
        (PurePattern domain variable annotation)
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
    :: (Foldable domain, Functor domain, Ord variable)
    => PurePattern domain variable annotation
    -> Set.Set variable
pureAllVariables = Recursive.fold pureMergeVariables

{- | @synthetic@ is an algebra for the free variables of a pattern.

Use @synthetic@ with 'Kore.Annotation.synthesize' to annotate a pattern with its
free variables as a synthetic attribute.

 -}
synthetic
    :: (Foldable domain, Ord variable)
    => CofreeF (PatternF domain variable) a (Set.Set variable)
    -> Set.Set variable
synthetic (_ :< patternHead) =
    case patternHead of
        ExistsF Exists { existsVariable, existsChild } ->
            Set.delete existsVariable existsChild
        ForallF Forall { forallVariable, forallChild } ->
            Set.delete forallVariable forallChild
        VariableF variable ->
            Set.singleton variable
        _ -> Foldable.foldl' Set.union Set.empty patternHead

{-# INLINE synthetic #-}
