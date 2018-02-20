module Data.Kore.ASTVerifier.SortVerifier
    (buildDeclaredSortVariables,
    buildDeclaredUnifiedSortVariables,
    verifySortUsage) where

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.Error
import qualified Data.Set                    as Set
import           Data.Typeable               (Typeable)

verifySortUsage
    :: IsMeta a
    => (Id a -> Either (Error VerifyError) (SortDescription a))
    -> Set.Set UnifiedSortVariable
    -> Sort a
    -> Either (Error VerifyError) VerifySuccess
verifySortUsage _ declaredSortVariables (SortVariableSort variable)
  = do
    koreFailWhen (not (unifiedVariable `Set.member` declaredSortVariables))
        ("Sort variable '" ++ getId variableId ++ "' not declared.")
    verifySuccess
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
  = do
    koreFailWhen (actualSortCount /= declaredSortCount)
        (  "Expected "
        ++ show declaredSortCount
        ++ " sort arguments, but got "
        ++ show actualSortCount
        ++ "."
        )
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
    koreFailWhen (unifiedVariable `Set.member` variables)
                (  "Duplicated sort variable: '"
                ++ extractVariableName unifiedVariable
                ++ "'.")
    return (Set.insert unifiedVariable variables)
  where
    extractVariableName (ObjectSortVariable variable) =
        getId (getSortVariable variable)
    extractVariableName (MetaSortVariable variable) =
        getId (getSortVariable variable)
