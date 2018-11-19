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
    ( freeVariables
    , freePureVariables
    , allVariables
    , pureAllVariables
    ) where

import qualified Control.Monad.RWS.Strict as Monad.RWS
import           Data.Foldable
                 ( fold )
import           Data.Functor.Foldable
                 ( Fix, cata )
import qualified Data.Functor.Foldable as Functor.Foldable
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.MetaOrObject

{- | The free variables of a pure pattern.
 -}
freePureVariables
    :: (Foldable domain, Functor domain, Ord (variable level))
    => PureMLPattern level domain variable
    -> Set (variable level)
freePureVariables root =
    let (free, ()) =
            Monad.RWS.execRWS
                (freePureVariables1 root)
                Set.empty  -- initial set of bound variables
                Set.empty  -- initial set of free variables
    in
        free
  where
    unlessM m go = m >>= \b -> if b then return () else go
    isBound v = Monad.RWS.asks (Set.member v)
    recordFree v = Monad.RWS.modify' (Set.insert v)

    freePureVariables1 recursive =
        case Functor.Foldable.project recursive of
            VariablePattern v -> unlessM (isBound v) (recordFree v)
            ExistsPattern Exists { existsVariable, existsChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert existsVariable)
                    -- descend into the bound pattern
                    (freePureVariables1 existsChild)
            ForallPattern Forall { forallVariable, forallChild } ->
                Monad.RWS.local
                    -- record the bound variable
                    (Set.insert forallVariable)
                    -- descend into the bound pattern
                    (freePureVariables1 forallChild)
            p -> mapM_ freePureVariables1 p

{-| 'freeVariables' extracts the set of free variables of a pattern. -}
freeVariables
    ::  ( UnifiedPatternInterface pat
        , Functor (pat dom var)
        , Foldable dom
        , Ord (var Object)
        , Ord (var Meta)
        )
    => Fix (pat dom var) -> Set.Set (Unified var)
freeVariables = patternBottomUpVisitor freeVarsVisitor
    where
    freeVarsVisitor (VariablePattern v) = Set.singleton (asUnified v)
    freeVarsVisitor (ExistsPattern e) =
        Set.delete (asUnified (existsVariable e)) (existsChild e)
    freeVarsVisitor (ForallPattern f) =
        Set.delete (asUnified (forallVariable f)) (forallChild f)
    freeVarsVisitor p = fold p  -- default rule

{-| 'allVariables' extracts all variables in a pattern as a set, regardless of
whether they are quantified or not.
-}
allVariables
    ::  ( UnifiedPatternInterface pat
        , Functor (pat dom var)
        , Foldable dom
        , Ord (var Object)
        , Ord (var Meta)
        )
    => Fix (pat dom var) -> Set.Set (Unified var)
allVariables = patternBottomUpVisitor allVarsVisitor
  where
    allVarsVisitor (VariablePattern v) = Set.singleton (asUnified v)
    allVarsVisitor (ExistsPattern e) =
        Set.insert (asUnified (existsVariable e)) (existsChild e)
    allVarsVisitor (ForallPattern f) =
        Set.insert (asUnified (forallVariable f)) (forallChild f)
    allVarsVisitor p = fold p  -- default rule

pureMergeVariables
    :: (Foldable dom, Ord (var level))
    => Pattern level dom var (Set.Set (var level)) -> Set.Set (var level)
pureMergeVariables (VariablePattern v) = Set.singleton v
pureMergeVariables (ExistsPattern e) =
    Set.insert (existsVariable e) (existsChild e)
pureMergeVariables (ForallPattern f) =
    Set.insert (forallVariable f) (forallChild f)
pureMergeVariables p = fold p  -- default rule

{-| 'pureAllVariables' extracts all variables of a given level in a pattern as a
set, regardless of whether they are quantified or not.
-}
pureAllVariables
    :: (Foldable dom, Functor dom, Ord (var level))
    => PureMLPattern level dom var -> Set.Set (var level)
pureAllVariables = cata pureMergeVariables
