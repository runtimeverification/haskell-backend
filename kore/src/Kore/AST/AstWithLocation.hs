{- |
Module      : Kore.AST.AstWithLocation
Description : Class for extracting locations from AST terms.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.AST.AstWithLocation (
    AstWithLocation (..),
    prettyPrintLocationFromAst,
) where

import Data.Text (
    Text,
 )
import Kore.Syntax
import Kore.Syntax.Definition
import Prelude.Kore

{- | 'AstWithLocation' should be implemented by all AST terms that have
an 'AstLocation'.
-}
class AstWithLocation awl where
    locationFromAst :: awl -> AstLocation

prettyPrintLocationFromAst ::
    AstWithLocation astWithLocation =>
    astWithLocation ->
    Text
prettyPrintLocationFromAst = prettyPrintAstLocation . locationFromAst

instance AstWithLocation AstLocation where
    locationFromAst = id

instance AstWithLocation Id where
    locationFromAst = idLocation

instance AstWithLocation SortVariable where
    locationFromAst = locationFromAst . getSortVariable

instance AstWithLocation SortActual where
    locationFromAst = locationFromAst . sortActualName

instance AstWithLocation Sort where
    locationFromAst (SortVariableSort sortVariable) =
        locationFromAst sortVariable
    locationFromAst (SortActualSort sortActual) =
        locationFromAst sortActual

instance AstWithLocation VariableName where
    locationFromAst = locationFromAst . base

instance AstWithLocation variable => AstWithLocation (ElementVariableName variable) where
    locationFromAst = locationFromAst . unElementVariableName

instance AstWithLocation variable => AstWithLocation (SetVariableName variable) where
    locationFromAst = locationFromAst . unSetVariableName

instance AstWithLocation variable => AstWithLocation (SomeVariableName variable) where
    locationFromAst = foldSomeVariableName (pure locationFromAst)

instance AstWithLocation variable => AstWithLocation (Variable variable) where
    locationFromAst = locationFromAst . variableName

instance AstWithLocation Alias where
    locationFromAst = locationFromAst . aliasConstructor

instance AstWithLocation SymbolOrAlias where
    locationFromAst = locationFromAst . symbolOrAliasConstructor

instance AstWithLocation Symbol where
    locationFromAst = locationFromAst . symbolConstructor

instance
    AstWithLocation variable =>
    AstWithLocation (PatternF variable child)
    where
    locationFromAst =
        \case
            AndF And{andSort} -> locationFromAst andSort
            ApplicationF Application{applicationSymbolOrAlias} ->
                locationFromAst applicationSymbolOrAlias
            BottomF Bottom{bottomSort} -> locationFromAst bottomSort
            CeilF Ceil{ceilResultSort} -> locationFromAst ceilResultSort
            DomainValueF domain -> locationFromAst $ domainValueSort domain
            EqualsF Equals{equalsResultSort} ->
                locationFromAst equalsResultSort
            ExistsF Exists{existsSort} -> locationFromAst existsSort
            FloorF Floor{floorResultSort} ->
                locationFromAst floorResultSort
            ForallF Forall{forallSort} -> locationFromAst forallSort
            IffF Iff{iffSort} -> locationFromAst iffSort
            ImpliesF Implies{impliesSort} ->
                locationFromAst impliesSort
            InF In{inResultSort} ->
                locationFromAst inResultSort
            MuF Mu{muVariable} -> locationFromAst muVariable
            NextF Next{nextSort} -> locationFromAst nextSort
            NotF Not{notSort} -> locationFromAst notSort
            NuF Nu{nuVariable} -> locationFromAst nuVariable
            OrF Or{orSort} -> locationFromAst orSort
            RewritesF Rewrites{rewritesSort} ->
                locationFromAst rewritesSort
            StringLiteralF _ -> AstLocationUnknown
            TopF Top{topSort} -> locationFromAst topSort
            VariableF (Const variable) -> locationFromAst variable
            InhabitantF Inhabitant{inhSort} -> locationFromAst inhSort
