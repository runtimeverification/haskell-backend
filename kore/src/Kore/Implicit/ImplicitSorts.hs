{-|
Module      : Kore.Implicit.ImplicitSorts
Description : Haskell definitions for the implicit Kore 'Meta' sorts.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

module Kore.Implicit.ImplicitSorts where

import Kore.AST.MetaOrObject
import Kore.Implicit.ImplicitSortsImpl
import Kore.Sort

-- TODO(virgil-serbanuta): Add tests for "defined but not used" symbols
charMetaSort     :: Sort Meta
charListMetaSort :: Sort Meta
(charMetaSort, charListMetaSort) = defineMetaSort CharSort

sortMetaSort     :: Sort Meta
sortListMetaSort :: Sort Meta
(sortMetaSort, sortListMetaSort) = defineMetaSort SortSort

symbolMetaSort     :: Sort Meta
symbolListMetaSort :: Sort Meta
(symbolMetaSort, symbolListMetaSort) = defineMetaSort SymbolSort

variableMetaSort     :: Sort Meta
variableListMetaSort :: Sort Meta
(variableMetaSort, variableListMetaSort) = defineMetaSort VariableSort

patternMetaSort     :: Sort Meta
patternListMetaSort :: Sort Meta
(patternMetaSort, patternListMetaSort) = defineMetaSort PatternSort

stringMetaSort :: Sort Meta
stringMetaSort = charListMetaSort

predicateSortActual :: SortActual level
predicateSortActual =
    SortActual
        { sortActualName = "_PREDICATE"
        , sortActualSorts = []
        }

{- | Placeholder sort for constructing new predicates.

The final predicate sort is unknown until the predicate is attached to a
pattern.
 -}
predicateSort :: Sort level
{- TODO PREDICATE (thomas.tuegel):

Add a constructor

> data Sort level = ... | FlexibleSort

to use internally as a placeholder where the predicate sort is not yet
known. Using the sort _PREDICATE{} is a kludge; the backend will melt down if
the user tries to define a sort named _PREDICATE{}. (At least, this is not
actually a valid identifier in Kore.)

Until this is fixed, the identifier _PREDICATE is reserved in
Kore.ASTVerifier.DefinitionVerifier.indexImplicitModule.

-}
predicateSort = SortActualSort predicateSortActual
