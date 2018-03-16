{-|
Module      : Data.Kore.ASTVerifier.AttributesVerifier
Description : Tools for verifying the wellformedness of Kore 'Attributes'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.AttributesVerifier (verifyAttributes) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.PatternVerifier
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import qualified Data.Set                              as Set

{-|'verifyAttributes' verifies the weldefinedness of the given attributes.
-}
verifyAttributes
    :: Attributes
    -> IndexedModule
    -- ^ Module with the declarations visible in these atributes.
    -> Set.Set (Unified SortVariable)
    -- ^ Sort variables visible in these atributes.
    -> Either (Error VerifyError) VerifySuccess
verifyAttributes (Attributes patterns) indexedModule sortVariables = do
    withContext
        "attributes"
        (mapM_
            (\p -> verifyPattern p Nothing indexedModule sortVariables)
            patterns
        )
    verifySuccess
