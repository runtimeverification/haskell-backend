{-|
Module      : Kore.Implicit.ImplicitSortsImpl
Description : Infrastructure for defining the implicit Kore 'Meta' sorts.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Implicit.ImplicitSortsImpl (defineMetaSort) where

import Kore.AST.Builders
import Kore.AST.MetaOrObject
import Kore.AST.Pure

{-|'defineMetaSort' is a helper function for defining meta sorts together
with their constructors, helper functions and axioms.
-}
defineMetaSort
    :: MetaBasicSortType
    -> ( Sort Meta
       , Sort Meta
       )
defineMetaSort sortType =
    (objectSort, listSort)
  where
    objectSortType = MetaBasicSortType sortType
    listSortType =  MetaListSortType sortType
    objectSort = sort_ objectSortType
    listSort = sort_ listSortType
