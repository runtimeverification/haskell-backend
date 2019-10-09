{-|
Module      : Kore.AST.AstWithLocation
Description : Class for extracting locations from AST terms.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.AST.AstWithLocation
    ( AstWithLocation(..)
    , prettyPrintLocationFromAst
    ) where

import Data.Text
    ( Text
    )

import Kore.Syntax
import Kore.Syntax.Definition
import Kore.Syntax.PatternF
    ( PatternF (..)
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

{-| 'AstWithLocation' should be implemented by all AST terms that have
an 'AstLocation'.
-}
class AstWithLocation awl where
    locationFromAst :: awl -> AstLocation
    updateAstLocation :: awl -> AstLocation -> awl

prettyPrintLocationFromAst
    :: AstWithLocation astWithLocation
    => astWithLocation -> Text
prettyPrintLocationFromAst = prettyPrintAstLocation . locationFromAst

instance AstWithLocation AstLocation where
    locationFromAst = id
    updateAstLocation _ loc = loc

instance AstWithLocation Id where
    locationFromAst = idLocation
    updateAstLocation id' loc = id' { idLocation = loc }

instance AstWithLocation SortVariable where
    locationFromAst = locationFromAst . getSortVariable
    updateAstLocation (SortVariable v) loc =
        SortVariable (updateAstLocation v loc)

instance AstWithLocation SortActual where
    locationFromAst = locationFromAst . sortActualName
    updateAstLocation sa loc =
        sa { sortActualName = updateAstLocation (sortActualName sa) loc }

instance AstWithLocation Sort where
    locationFromAst (SortVariableSort sortVariable) =
        locationFromAst sortVariable
    locationFromAst (SortActualSort sortActual) =
        locationFromAst sortActual
    updateAstLocation (SortVariableSort sortVariable) loc =
        SortVariableSort (updateAstLocation sortVariable loc)
    updateAstLocation (SortActualSort sortActual) loc =
        SortActualSort (updateAstLocation sortActual loc)

instance AstWithLocation Variable where
    locationFromAst = locationFromAst . variableName
    updateAstLocation var loc =
        var {variableName = updateAstLocation (variableName var) loc}
instance
    AstWithLocation variable =>
    AstWithLocation (UnifiedVariable variable)
  where
    locationFromAst (ElemVar v) = locationFromAst . getElementVariable $ v
    locationFromAst (SetVar v) = locationFromAst . getSetVariable $ v
    updateAstLocation var loc = fmap (`updateAstLocation` loc) var

instance AstWithLocation Alias where
    locationFromAst = locationFromAst . aliasConstructor
    updateAstLocation al loc =
        al { aliasConstructor = updateAstLocation (aliasConstructor al) loc }

instance AstWithLocation SymbolOrAlias where
    locationFromAst = locationFromAst . symbolOrAliasConstructor
    updateAstLocation sal loc =
        sal
            { symbolOrAliasConstructor =
                updateAstLocation (symbolOrAliasConstructor sal) loc
            }

instance AstWithLocation Symbol where
    locationFromAst = locationFromAst . symbolConstructor
    updateAstLocation s loc =
        s { symbolConstructor = updateAstLocation (symbolConstructor s) loc }

instance
    AstWithLocation variable =>
    AstWithLocation (PatternF variable child)
  where
    locationFromAst =
        \case
            AndF And { andSort } -> locationFromAst andSort
            ApplicationF Application { applicationSymbolOrAlias } ->
                locationFromAst applicationSymbolOrAlias
            BottomF Bottom { bottomSort } -> locationFromAst bottomSort
            CeilF Ceil { ceilResultSort } -> locationFromAst ceilResultSort
            DomainValueF domain -> locationFromAst $ domainValueSort domain
            EqualsF Equals { equalsResultSort } ->
                locationFromAst equalsResultSort
            ExistsF Exists { existsSort } -> locationFromAst existsSort
            FloorF Floor { floorResultSort } ->
                locationFromAst floorResultSort
            ForallF Forall { forallSort } -> locationFromAst forallSort
            IffF Iff { iffSort } -> locationFromAst iffSort
            ImpliesF Implies { impliesSort } ->
                locationFromAst impliesSort
            InF In { inResultSort } ->
                locationFromAst inResultSort
            MuF Mu { muVariable = SetVariable variable } ->
                locationFromAst variable
            NextF Next { nextSort } -> locationFromAst nextSort
            NotF Not { notSort } -> locationFromAst notSort
            NuF Nu { nuVariable = SetVariable variable } ->
                locationFromAst variable
            OrF Or { orSort } -> locationFromAst orSort
            RewritesF Rewrites { rewritesSort } ->
                locationFromAst rewritesSort
            StringLiteralF _ -> AstLocationUnknown
            TopF Top { topSort } -> locationFromAst topSort
            VariableF (Const variable) -> locationFromAst variable
            InhabitantF Inhabitant { inhSort } -> locationFromAst inhSort

    updateAstLocation = undefined
