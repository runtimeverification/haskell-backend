module Data.Kore.ASTVerifier.AttributesVerifier (verifyAttributes) where

import           Data.Kore.AST
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.PatternVerifier
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import qualified Data.Set                              as Set

verifyAttributes
    :: Attributes
    -> IndexedModule
    -> Set.Set UnifiedSortVariable
    -> Either (Error VerifyError) VerifySuccess
verifyAttributes (Attributes patterns) indexedModule sortVariables = do
    withContext
        "attributes"
        (mapM_
            (\p -> verifyPattern p Nothing indexedModule sortVariables)
            patterns
        )
    verifySuccess
