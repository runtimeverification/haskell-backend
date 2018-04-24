{-|
Module      : Data.Kore.ASTVerifier.AttributesVerifier
Description : Tools for verifying the wellformedness of Kore 'Attributes'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Data.Kore.ASTVerifier.AttributesVerifier (verifyAttributes,
                                                 AttributesVerification (..))
  where

import           Data.Kore.AST.Common                  (Attributes (..))
import           Data.Kore.AST.Kore                    (KoreAttributes,
                                                        UnifiedSortVariable)
import           Data.Kore.AST.MetaOrObject            (asUnified)
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.PatternVerifier
import           Data.Kore.Error
import           Data.Kore.Implicit.Attributes         (attributeObjectSort)
import           Data.Kore.IndexedModule.IndexedModule
import qualified Data.Set                              as Set

data AttributesVerification
    = VerifyAttributes KoreIndexedModule | DoNotVerifyAttributes

{-|'verifyAttributes' verifies the weldefinedness of the given attributes.
-}
verifyAttributes
    :: KoreAttributes
    -> Set.Set UnifiedSortVariable
    -- ^ Sort variables visible in these atributes.
    -> AttributesVerification
    -- ^ Module with the declarations visible in these atributes.
    -> Either (Error VerifyError) VerifySuccess
verifyAttributes
    (Attributes patterns)
    sortVariables
    (VerifyAttributes indexedModule)
  = do
    withContext
        "attributes"
        (mapM_
            (\p ->
                verifyPattern
                    p
                    (Just (asUnified attributeObjectSort))
                    indexedModule
                    sortVariables
            )
            patterns
        )
    verifySuccess
verifyAttributes _ _ DoNotVerifyAttributes =
    verifySuccess
