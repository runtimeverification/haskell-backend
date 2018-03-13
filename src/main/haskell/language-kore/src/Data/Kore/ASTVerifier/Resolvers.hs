{-|
Module      : Data.Kore.ASTVerifier.Resolvers
Description : Tools for resolving IDs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.Resolvers ( resolveMetaSort
                                       , resolveObjectSort
                                       ) where

import           Data.Kore.AST.Common
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule

import qualified Data.Map                              as Map

{-|'resolveMetaSort' resolves a meta sort given its id. -}
resolveMetaSort
    :: IndexedModule
    -- ^ Module containing the visible declarations.
    -> Id Meta
    -- ^ The ID of the sort.
    -> Either (Error VerifyError) (SortDescription Meta)
resolveMetaSort = resolveSort indexedModuleMetaSortDescriptions

{-|'resolveObjectSort' resolves an object sort given its id. -}
resolveObjectSort
    :: IndexedModule
    -- ^ Module containing the visible declarations.
    -> Id Object
    -- ^ The ID of the sort.
    -> Either (Error VerifyError) (SortDescription Object)
resolveObjectSort = resolveSort indexedModuleObjectSortDescriptions

{-|'resolveSort' resolves a sort given its id. -}
resolveSort
    :: (IndexedModule -> Map.Map (Id level) (SortDescription level))
    -- ^ Extracts the sort map to use.
    -> IndexedModule
    -- ^ Module containing the visible declarations.
    -> Id level
    -- ^ The ID of the sort.
    -> Either (Error VerifyError) (SortDescription level)
resolveSort mapExtractor indexedModule sortId =
    case resolveThing mapExtractor indexedModule sortId of
        Nothing -> koreFail ("Sort '" ++ getId sortId ++  "' not declared.")
        Just sortDescription -> Right sortDescription
