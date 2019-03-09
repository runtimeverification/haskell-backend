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

import qualified Control.Lens as Lens

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.MLPatterns
import Kore.AST.Sentence
import Kore.Domain.Class
import Kore.Sort

{-| 'AstWithLocation' should be implemented by all AST terms that have
an 'AstLocation'.
-}
class AstWithLocation awl where
    locationFromAst :: awl -> AstLocation
    updateAstLocation :: awl -> AstLocation -> awl

prettyPrintLocationFromAst
    :: AstWithLocation astWithLocation
    => astWithLocation -> String
prettyPrintLocationFromAst = prettyPrintAstLocation . locationFromAst

instance
    (AstWithLocation (thing Object), AstWithLocation (thing Meta))
    => AstWithLocation (Unified thing)
  where
    locationFromAst (UnifiedObject t) = locationFromAst t
    locationFromAst (UnifiedMeta t)   = locationFromAst t
    updateAstLocation (UnifiedObject t) loc =
        UnifiedObject (updateAstLocation t loc)
    updateAstLocation (UnifiedMeta t) loc =
        UnifiedMeta (updateAstLocation t loc)

instance AstWithLocation AstLocation where
    locationFromAst = id
    updateAstLocation _ loc = loc

instance AstWithLocation (Id level) where
    locationFromAst = idLocation
    updateAstLocation id' loc = id' { idLocation = loc }

instance AstWithLocation (SortVariable level) where
    locationFromAst = locationFromAst . getSortVariable
    updateAstLocation (SortVariable v) loc =
        SortVariable (updateAstLocation v loc)

instance AstWithLocation (SortActual level) where
    locationFromAst = locationFromAst . sortActualName
    updateAstLocation sa loc =
        sa { sortActualName = updateAstLocation (sortActualName sa) loc }

instance AstWithLocation (Sort level) where
    locationFromAst (SortVariableSort sortVariable) =
        locationFromAst sortVariable
    locationFromAst (SortActualSort sortActual) =
        locationFromAst sortActual
    updateAstLocation (SortVariableSort sortVariable) loc =
        SortVariableSort (updateAstLocation sortVariable loc)
    updateAstLocation (SortActualSort sortActual) loc =
        SortActualSort (updateAstLocation sortActual loc)

instance AstWithLocation (Variable level) where
    locationFromAst = locationFromAst . variableName
    updateAstLocation var loc =
        var {variableName = updateAstLocation (variableName var) loc}

instance AstWithLocation (Alias level) where
    locationFromAst = locationFromAst . aliasConstructor
    updateAstLocation al loc =
        al { aliasConstructor = updateAstLocation (aliasConstructor al) loc }

instance AstWithLocation (SymbolOrAlias level) where
    locationFromAst = locationFromAst . symbolOrAliasConstructor
    updateAstLocation sal loc =
        sal
            { symbolOrAliasConstructor =
                updateAstLocation (symbolOrAliasConstructor sal) loc
            }

instance AstWithLocation (Symbol level) where
    locationFromAst = locationFromAst . symbolConstructor
    updateAstLocation s loc =
        s { symbolConstructor = updateAstLocation (symbolConstructor s) loc }

instance
    (Domain domain, AstWithLocation (variable level)) =>
    AstWithLocation (Pattern level domain variable child)
  where
    locationFromAst = applyPatternFunction PatternFunction
        { patternFunctionML = locationFromAst . getMLPatternResultSort
        , patternFunctionMLBinder = locationFromAst . getBinderPatternSort
        , applicationFunction = locationFromAst . applicationSymbolOrAlias
        , variableFunction = locationFromAst
        , domainValueFunction =
            locationFromAst . domainValueSort . Lens.view lensDomainValue
        , stringFunction = const AstLocationUnknown
        , charFunction = const AstLocationUnknown
        }
    updateAstLocation = undefined
