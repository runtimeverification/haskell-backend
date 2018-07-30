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

import Data.Proxy
       (Proxy)

import Kore.AST.Common
import Kore.AST.MetaOrObject
       ( Object )
import Kore.AST.Sentence
import Kore.AST.Kore
       ( KorePattern, applyKorePattern )
import Kore.ASTVerifier.Error
import Kore.Error

{--| Whether we should verify attributes and, when verifying, the module with
declarations visible in these atributes. --}
data AttributesVerification atts
    = VerifyAttributes (Proxy atts)
    | DoNotVerifyAttributes

{-|'verifyAttributes' verifies the wellformedness of the given attributes.
-}
verifyAttributes
    :: Attributes
    -> AttributesVerification atts
    -> Either (Error VerifyError) VerifySuccess
verifyAttributes
    (Attributes patterns)
    (VerifyAttributes _)
  = do
    withContext
        "attributes"
        (mapM_
            (applyKorePattern
                (const (koreFail "Meta attributes are not supported"))
                verifyAttributePattern
            )
            patterns
        )
    verifySuccess
verifyAttributes _ DoNotVerifyAttributes =
    verifySuccess

verifyAttributePattern
    :: Pattern Object variable (KorePattern variable)
    -> Either (Error VerifyError) VerifySuccess
verifyAttributePattern (ApplicationPattern _) = verifySuccess
verifyAttributePattern _
     = koreFail "Non-application attributes are not supported"
