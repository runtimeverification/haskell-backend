{-|
Module      : Data.Kore.ASTVerifier.SortVerifier
Description : Tools for verifying the wellformedness of a Kore 'Sort'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.SortVerifier (verifySort) where

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import qualified Data.Set                              as Set

{-|'verifySort' verifies the welformedness of a Kore 'Sort'. -}
verifySort
    :: IsMeta a
    => (Id a -> Either (Error VerifyError) (SortDescription a))
    -- ^ Provides a sort's description.
    -> Set.Set UnifiedSortVariable
    -- ^ Sort variables visible here.
    -> Sort a
    -> Either (Error VerifyError) VerifySuccess
verifySort _ declaredSortVariables (SortVariableSort variable)
  = do
    koreFailWhen (not (unifiedVariable `Set.member` declaredSortVariables))
        ("Sort variable '" ++ getId variableId ++ "' not declared.")
    verifySuccess
  where
    variableId = getSortVariable variable
    unifiedVariable = asUnified variable
verifySort findSortDescription declaredSortVariables (SortActualSort sort)
  =
    withContext
        ("sort '" ++ getId (sortActualName sort) ++ "'")
        ( do
            sortDescription <- findSortDescription (sortActualName sort)
            verifySortMatchesDeclaration
                findSortDescription
                declaredSortVariables
                sort
                sortDescription
        )

verifySortMatchesDeclaration
    :: IsMeta a
    => (Id a -> Either (Error VerifyError) (SortDescription a))
    -> Set.Set UnifiedSortVariable
    -> SortActual a
    -> SortDescription a
    -> Either (Error VerifyError) VerifySuccess
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
    declaredSortCount = length (sortDescriptionParameters sortDescription)
