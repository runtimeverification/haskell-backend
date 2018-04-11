module Data.Kore.Implicit.ImplicitSortsImpl where
{-|
Module      : Data.Kore.Implicit.ImplicitSortsImpl
Description : Infrastructure for defining the implicit Kore 'Meta' sorts.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Implicit.ImplicitKoreImpl     (equalsAxiom,
                                                          parameterizedAxiom,
                                                          parameterizedEqualsAxiom)
import           Data.Kore.Implicit.ImplicitVarsInternal
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.Builders

{-|'defineMetaSort' is a helper function for defining meta sorts together
with their constructors, helper functions and axioms.
-}
defineMetaSort
    :: MetaBasicSortType
    -> ( Sort Meta
       , Sort Meta
       , MetaSentenceSymbol
       , MetaPatternStub
       , MetaSentenceSymbol
       , [MetaPatternStub] -> MetaPatternStub
       , MetaSentenceSymbol
       , [MetaPatternStub] -> MetaPatternStub
       , MetaSentenceSymbol
       , [Sort Meta] -> [MetaPatternStub] -> MetaPatternStub
       , MetaSentenceSymbol
       , [MetaPatternStub] -> MetaPatternStub
       , [MetaSentenceAxiom]
       )
defineMetaSort sortType =
    ( objectSort
    , listSort
    , emptyList
    , emptyListA
    , listConstructor
    , listConstructorA
    , append
    , appendA
    , inList
    , inListA
    , delete
    , deleteA
        -- inList
    ,   [ parameterizedAxiom [pS] (not_ (inListA [spS] [vs, emptyListA]))
        , parameterizedEqualsAxiom [pS]
            (inListA [spS] [vs, listConstructorA [vs', vS]])
            (or_
                (equalsS_ objectSort vs vs')
                (inListA [spS] [vs, vS])
            )
        -- append
        , equalsAxiom (appendA [emptyListA, vS]) vS
        , equalsAxiom
            (appendA [listConstructorA [vs, vS'], vS])
            (listConstructorA [vs, appendA [vS', vS]])
        -- delete
        , equalsAxiom
            (deleteA [vs, emptyListA])
            emptyListA
        , equalsAxiom
            (deleteA [vs, listConstructorA [vs', vS]])
            (or_
                (and_ (equalsS_ objectSort vs vs') (deleteA [vs, vS]))
                (and_
                    (not_ (equalsS_ objectSort vs vs'))
                    (listConstructorA [vs', deleteA [vs, vS]])
                )
            )
        ]
    )
  where
    objectSortType = MetaBasicSortType sortType
    listSortType =  MetaListSortType sortType
    listSortName =  metaSortTypeString listSortType
    objectSort = sort_ objectSortType
    listSort = sort_ listSortType
    emptyList = symbol_ ("#nil" ++ listSortName) [] listSort
    emptyListA = applyS emptyList []
    listConstructor =
        symbol_ ("#cons" ++ listSortName) [objectSort, listSort] listSort
    listConstructorA = applyS listConstructor
    append =
        symbol_ ("#append" ++ listSortName) [listSort, listSort] listSort
    appendA = applyS append
    inList =
        parameterizedSymbol_
            ("#in" ++ listSortName) [pS] [objectSort, listSort] spS
    inListA = applyPS inList
    delete =
        symbol_ ("#delete" ++ listSortName) [objectSort, listSort] listSort
    deleteA = applyS delete
