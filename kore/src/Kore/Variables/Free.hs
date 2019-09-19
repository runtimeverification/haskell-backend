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
    ) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Control.Monad.Extra as Monad
import qualified Control.Monad.RWS.Strict as Monad.RWS
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import Data.Set
    ( Set
    )
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
            VariableF (Const variable) ->
                Monad.unlessM (isBound variable) (recordFree variable)
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
            MuF Mu { muVariable, muChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (SetVar muVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 muChild)
            NuF Nu { nuVariable, nuChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (SetVar nuVariable))
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
        VariableF (Const variable) -> Set.singleton variable
        ExistsF Exists { existsVariable, existsChild } ->
            Set.insert (ElemVar existsVariable) existsChild
        ForallF Forall { forallVariable, forallChild } ->
            Set.insert (ElemVar forallVariable) forallChild
        MuF Mu { muVariable, muChild } ->
            Set.insert (SetVar muVariable) muChild
        NuF Nu { nuVariable, nuChild } ->
            Set.insert (SetVar nuVariable) nuChild
        p -> Foldable.foldl' Set.union Set.empty p

{-| 'pureAllVariables' extracts all variables of a given level in a pattern as a
set, regardless of whether they are quantified or not.
-}
pureAllVariables
    :: Ord variable
    => Pattern variable annotation
    -> Set.Set (UnifiedVariable variable)
pureAllVariables = Recursive.fold pureMergeVariables
