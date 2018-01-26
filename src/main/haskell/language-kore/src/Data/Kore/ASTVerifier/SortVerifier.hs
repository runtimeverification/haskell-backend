module Data.Kore.ASTVerifier.SortVerifier
    (buildDeclaredSortVariables,
    buildDeclaredUnifiedSortVariables,
    verifySortUsage) where

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.Error
import qualified Data.Set as Set
import           Data.Typeable (Typeable)

verifySortUsage
    :: IsMeta a
    => (Id a -> Either (Error VerifyError) (SortDescription a))
    -> Set.Set UnifiedSortVariable
    -> Sort a
    -> Either (Error VerifyError) VerifySuccess
verifySortUsage _ declaredSortVariables (SortVariableSort variable) =
    withContext
        ("sort variable '" ++ getId variableId ++ "'")
        (if unifiedVariable `Set.member` declaredSortVariables
            then verifySuccess
            else
                koreFail
                    ("Sort variable '" ++ getId variableId ++ "' not declared.")
        )
  where
    variableId = getSortVariable variable
    unifiedVariable = asUnifiedSortVariable variable
verifySortUsage findSortDescription declaredSortVariables (SortActualSort sort)
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
  =
    if actualSortCount /= declaredSortCount
        then koreFail
                (  "Expected "
                ++ show declaredSortCount
                ++ " sort arguments, but got "
                ++ show actualSortCount
                ++ "."
                )
        else do
            mapM_
                (verifySortUsage findSortDescription declaredSortVariables)
                (sortActualSorts sort)
            verifySuccess
  where
    actualSortCount = length (sortActualSorts sort)
    declaredSortCount = length (sortDescriptionParameters sortDescription)

buildDeclaredSortVariables
    :: Typeable a
    => [SortVariable a]
    -> Either (Error VerifyError) (Set.Set UnifiedSortVariable)
buildDeclaredSortVariables variables =
    buildDeclaredUnifiedSortVariables
        (map asUnifiedSortVariable variables)

buildDeclaredUnifiedSortVariables
    :: [UnifiedSortVariable]
    -> Either (Error VerifyError) (Set.Set UnifiedSortVariable)
buildDeclaredUnifiedSortVariables [] = Right Set.empty
buildDeclaredUnifiedSortVariables (unifiedVariable : list) = do
    variables <- buildDeclaredUnifiedSortVariables list
    if unifiedVariable `Set.member` variables
        then koreFail
                (  "Duplicated sort variable: '"
                ++ extractVariableName unifiedVariable
                ++ "'.")
        else return (Set.insert unifiedVariable variables)
  where
    extractVariableName (ObjectSortVariable variable) =
        getId (getSortVariable variable)
    extractVariableName (MetaSortVariable variable) =
        getId (getSortVariable variable)
