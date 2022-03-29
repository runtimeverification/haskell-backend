{- |
Module      : Kore.Variables.Free
Description : Specifies the 'TermWithVariablesClass' which is meant to define
              a term with variables and exports 'freeVariables'
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Variables.Free (
    freePureVariables,
    pureAllVariables,
) where

import Control.Comonad.Trans.Cofree qualified as Cofree
import Control.Monad.Extra qualified as Monad
import Control.Monad.RWS.Strict qualified as Monad.RWS
import Data.Functor.Foldable qualified as Recursive
import Data.Set (
    Set,
 )
import Data.Set qualified as Set
import Kore.Syntax
import Prelude.Kore

-- | The free variables of a pure pattern.
freePureVariables ::
    Ord variable =>
    Pattern variable annotation ->
    Set (SomeVariable variable)
freePureVariables root =
    let (free, ()) =
            Monad.RWS.execRWS
                (freePureVariables1 root)
                Set.empty -- initial set of bound variables
                Set.empty -- initial set of free variables
     in free
  where
    isBound v = Monad.RWS.asks (Set.member v)
    recordFree v = Monad.RWS.modify' (Set.insert v)

    freePureVariables1 recursive =
        case Cofree.tailF (Recursive.project recursive) of
            VariableF (Const variable) ->
                Monad.unlessM (isBound variable) (recordFree variable)
            ExistsF Exists{existsVariable, existsChild} ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (mkSomeVariable existsVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 existsChild)
            ForallF Forall{forallVariable, forallChild} ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (mkSomeVariable forallVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 forallChild)
            MuF Mu{muVariable, muChild} ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (mkSomeVariable muVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 muChild)
            NuF Nu{nuVariable, nuChild} ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert (mkSomeVariable nuVariable))
                    -- descend into the bound pattern
                    (freePureVariables1 nuChild)
            p -> mapM_ freePureVariables1 p

pureMergeVariables ::
    Ord variable =>
    Base
        (Pattern variable annotation)
        (Set.Set (SomeVariable variable)) ->
    Set.Set (SomeVariable variable)
pureMergeVariables base =
    case Cofree.tailF base of
        VariableF (Const variable) -> Set.singleton variable
        ExistsF Exists{existsVariable, existsChild} ->
            Set.insert (mkSomeVariable existsVariable) existsChild
        ForallF Forall{forallVariable, forallChild} ->
            Set.insert (mkSomeVariable forallVariable) forallChild
        MuF Mu{muVariable, muChild} ->
            Set.insert (mkSomeVariable muVariable) muChild
        NuF Nu{nuVariable, nuChild} ->
            Set.insert (mkSomeVariable nuVariable) nuChild
        p -> foldl' Set.union Set.empty p

{- | 'pureAllVariables' extracts all variables of a given level in a pattern as a
set, regardless of whether they are quantified or not.
-}
pureAllVariables ::
    Ord variable =>
    Pattern variable annotation ->
    Set.Set (SomeVariable variable)
pureAllVariables = Recursive.fold pureMergeVariables
