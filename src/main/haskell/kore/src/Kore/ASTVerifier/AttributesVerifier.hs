{-|
Module      : Kore.ASTVerifier.AttributesVerifier
Description : Tools for verifying the wellformedness of Kore 'Attributes'.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.AttributesVerifier
    ( verifyAttributes
    , AttributesVerification (..)
    ) where

import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.MetaOrObject
       ( asUnified )
import Kore.AST.Sentence
import Kore.ASTVerifier.Error
import Kore.ASTVerifier.PatternVerifier
import Kore.Error
import Kore.Implicit.Attributes
       ( attributeObjectSort )
import Kore.IndexedModule.IndexedModule

{--| Whether we should verify attributes and, when verifying, the module with
declarations visible in these atributes. --}
data AttributesVerification
    = VerifyAttributes KoreIndexedModule | DoNotVerifyAttributes

{-|'verifyAttributes' verifies the wellformedness of the given attributes.
-}
verifyAttributes
    :: Attributes
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
