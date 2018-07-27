{-|
Module      : Kore.Variables.Free
Description : Specifies the 'TermWithVariablesClass' which is meant to define
              a term with variables and exports 'freeVariables'
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Variables.Free
    ( freeVariables
    , pureFreeVariables
    , allVariables
    , pureAllVariables
    ) where

import           Data.Foldable
                 ( fold )
import           Data.Functor.Foldable
                 ( Fix, cata )
import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.ASTTraversals

{-| 'freeVariables' extracts the set of free variables of a pattern. -}
freeVariables
    :: ( UnifiedPatternInterface pat
       , Functor (pat var)
       , Ord (var Object)
       , Ord (var Meta))
    => Fix (pat var) -> Set.Set (Unified var)
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
    :: ( UnifiedPatternInterface pat
       , Functor (pat var)
       , Ord (var Object)
       , Ord (var Meta))
    => Fix (pat var) -> Set.Set (Unified var)
allVariables = patternBottomUpVisitor allVarsVisitor
  where
    allVarsVisitor (VariablePattern v) = Set.singleton (asUnified v)
    allVarsVisitor (ExistsPattern e) =
        Set.insert (asUnified (existsVariable e)) (existsChild e)
    allVarsVisitor (ForallPattern f) =
        Set.insert (asUnified (forallVariable f)) (forallChild f)
    allVarsVisitor p = fold p  -- default rule

pureMergeVariables
    :: Ord (var level)
    => Pattern level var (Set.Set (var level)) -> Set.Set (var level)
pureMergeVariables (VariablePattern v) = Set.singleton v
pureMergeVariables (ExistsPattern e) =
    Set.insert (existsVariable e) (existsChild e)
pureMergeVariables (ForallPattern f) =
    Set.insert (forallVariable f) (forallChild f)
pureMergeVariables p = fold p  -- default rule

pureFreeVariables
    :: ( UnifiedPatternInterface pat
       , Functor (pat var)
       , Show (var Object)
       , Show (var Meta)
       , Ord (var Object)
       , Ord (var Meta)
       , MetaOrObject level)
    => proxy level -> Fix (pat var) -> Set.Set (var level)
pureFreeVariables proxy p =
    case isMetaOrObject proxy of
        IsMeta   -> metaVars `ifSetEmpty` unifiedObjectVars
        IsObject -> objectVars `ifSetEmpty` unifiedMetaVars
  where
    freeVars = freeVariables p
    isUnifiedMeta (UnifiedMeta _) = True
    isUnifiedMeta _               = False
    (unifiedMetaVars, unifiedObjectVars) = Set.partition isUnifiedMeta freeVars
    metaVars = Set.map (\ (UnifiedMeta v) -> v) unifiedMetaVars
    objectVars = Set.map (\ (UnifiedObject v) -> v) unifiedObjectVars

{-| 'pureAllVariables' extracts all variables of a given level in a pattern as a
set, regardless of whether they are quantified or not.
-}
pureAllVariables
    :: Ord (var level)
    => PureMLPattern level var -> Set.Set (var level)
pureAllVariables = cata pureMergeVariables

ifSetEmpty :: Show b => a -> Set.Set b -> a
ifSetEmpty a bs =
    if Set.null bs
        then a
        else error ("Expecting empty set " ++ show bs)
