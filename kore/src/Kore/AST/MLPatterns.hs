{-|
Module      : Kore.MLPatterns
Description : Data structures and functions for handling patterns uniformly.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.AST.MLPatterns
    ( getPatternResultSort
    , undefinedHeadSort
    ) where

import qualified Control.Lens as Lens

import Kore.AST.Kore
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.Domain.Class
import Kore.Implicit.ImplicitSorts

-- |'getPatternResultSort' retrieves the result sort of a pattern.
--
-- Since the sort of 'Application' patterns is not contained within
-- the term itself, it takes as firts argument a function yielding the
-- result sort corresponding to an application head.
getPatternResultSort
    :: (Domain domain, SortedVariable variable)
    => (SymbolOrAlias level -> ApplicationSorts level)
    -- ^Function to retrieve the sort of a given pattern Head
    -> Pattern level domain variable child
    -> Sort level
getPatternResultSort applicationSorts =
    \case
        AndPattern And { andSort } -> andSort
        ApplicationPattern Application { applicationSymbolOrAlias } ->
            applicationSortsResult (applicationSorts applicationSymbolOrAlias)
        BottomPattern Bottom { bottomSort } -> bottomSort
        CeilPattern Ceil { ceilResultSort } -> ceilResultSort
        DomainValuePattern domain ->
            domainValueSort (Lens.view lensDomainValue domain)
        EqualsPattern Equals { equalsResultSort } -> equalsResultSort
        ExistsPattern Exists { existsSort } -> existsSort
        FloorPattern Floor { floorResultSort } -> floorResultSort
        ForallPattern Forall { forallSort } -> forallSort
        IffPattern Iff { iffSort } -> iffSort
        ImpliesPattern Implies { impliesSort } -> impliesSort
        InPattern In { inResultSort } -> inResultSort
        NextPattern Next { nextSort } -> nextSort
        NotPattern Not { notSort } -> notSort
        OrPattern Or { orSort } -> orSort
        RewritesPattern Rewrites { rewritesSort } -> rewritesSort
        StringLiteralPattern _ -> stringMetaSort
        CharLiteralPattern _ -> charMetaSort
        TopPattern Top { topSort } -> topSort
        VariablePattern variable -> sortedVariableSort variable

-- |Sample argument function for 'getPatternResultSort', failing for all input.
undefinedHeadSort :: SymbolOrAlias level -> ApplicationSorts level
undefinedHeadSort _ =
    error "Application pattern sort currently undefined"
