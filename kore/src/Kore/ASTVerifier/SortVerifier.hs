{-|
Module      : Kore.ASTVerifier.SortVerifier
Description : Tools for verifying the wellformedness of a Kore 'Sort'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.SortVerifier (verifySort) where

import qualified Data.Set as Set

import Kore.AST.Error
import Kore.ASTVerifier.Error
import Kore.Error
import Kore.Syntax
import Kore.Syntax.Definition

{-|'verifySort' verifies the welformedness of a Kore 'Sort'. -}
verifySort
    :: MonadError (Error VerifyError) m
    => (Id -> m (SentenceSort patternType))
    -- ^ Provides a sortMetaSorts description.
    -> Set.Set SortVariable
    -- ^ Sort variables visible here.
    -> Sort
    -> m VerifySuccess
verifySort _ declaredSortVariables (SortVariableSort variable)
  = do
    koreFailWithLocationsWhen
        (Set.notMember variable declaredSortVariables)
        [variableId]
        ("Sort variable '" <> getId variableId <> "' not declared.")
    verifySuccess
  where
    variableId = getSortVariable variable
verifySort findSortDescription declaredSortVariables (SortActualSort sort)
  = do
    withLocationAndContext
        sortName
        ("sort '" <> getId (sortActualName sort) <> "'")
        ( do
            sortDescription <- findSortDescription sortName
            verifySortMatchesDeclaration
                findSortDescription
                declaredSortVariables
                sort
                sortDescription )
    koreFailWithLocationsWhen
        (sortIsMeta && sortActualSorts sort /= [])
        [sortName]
        (  "Malformed meta sort '"
        <> sortId
        <> "' with non-empty Parameter sorts."
        )
    verifySuccess
  where
    sortIsMeta = False
    sortName   = sortActualName sort
    sortId     = getId sortName

verifySortMatchesDeclaration
    :: MonadError (Error VerifyError) m
    => (Id -> m (SentenceSort patternType))
    -> Set.Set SortVariable
    -> SortActual
    -> SentenceSort patternType'
    -> m VerifySuccess
verifySortMatchesDeclaration
    findSortDescription declaredSortVariables sort sortDescription
  = do
    koreFailWhen (actualSortCount /= declaredSortCount)
        (  "Expected "
        ++ show declaredSortCount
        ++ " sort arguments, but got "
        ++ show actualSortCount
        ++ "."
        )
    mapM_
        (verifySort findSortDescription declaredSortVariables)
        (sortActualSorts sort)
    verifySuccess
  where
    actualSortCount = length (sortActualSorts sort)
    declaredSortCount = length (sentenceSortParameters sortDescription)
