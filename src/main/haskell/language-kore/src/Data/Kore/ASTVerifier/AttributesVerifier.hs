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

import           Data.Kore.AST.Common                  (AstLocation (..),
                                                        Attributes (..))
import           Data.Kore.AST.Kore                    (KoreAttributes)
import           Data.Kore.AST.MetaOrObject            (asUnified)
import           Data.Kore.ASTVerifier.Error
import           Data.Kore.ASTVerifier.PatternVerifier
import           Data.Kore.Error
import           Data.Kore.Implicit.Attributes         (attributeObjectSort)
import           Data.Kore.IndexedModule.IndexedModule
import qualified Data.Set                              as Set

{--| Whether we should verify attributes and, when verifying, the module with
declarations visible in these atributes. --}
data AttributesVerification
    = VerifyAttributes KoreIndexedModule | DoNotVerifyAttributes

{-|'verifyAttributes' verifies the wellformedness of the given attributes.
-}
verifyAttributes
    :: KoreAttributes
    -> AttributesVerification
    -> Either (Error VerifyError) VerifySuccess
verifyAttributes
    (Attributes patterns)
    (VerifyAttributes indexedModule)
  = do
    withContext
        "attributes"
        (mapM_
            (\p ->
                verifyPattern
                    p
                    (Just (asUnified (attributeObjectSort AstLocationNone)))
                    indexedModule
                    Set.empty
            )
            patterns
        )
    verifySuccess
verifyAttributes _ DoNotVerifyAttributes =
    verifySuccess
