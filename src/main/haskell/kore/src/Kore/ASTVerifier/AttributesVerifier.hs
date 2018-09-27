{-|
Module      : Kore.ASTVerifier.AttributesVerifier
Description : Tools for verifying the wellformedness of Kore 'Attributes'.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.AttributesVerifier
    ( verifyAttributes
    , verifyHookAttribute
    , AttributesVerification (..)
    ) where

import Data.Proxy
       ( Proxy )

import Kore.AST.Common
import Kore.AST.Kore
       ( KorePattern, applyKorePattern )
import Kore.AST.MetaOrObject
       ( Object )
import Kore.AST.Sentence
import Kore.ASTVerifier.Error
import Kore.Attribute.Parser
       ( parseAttributes )
import Kore.Builtin.Hook
       ( Hook (..) )
import Kore.Error
import Kore.IndexedModule.IndexedModule
       ( KoreIndexedModule )
import Kore.IndexedModule.Resolvers
       ( resolveHook )

{-| Whether we should verify attributes and, when verifying, the module with
declarations visible in these atributes. -}
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

{- | Verify that the @hook{}()@ attribute is present.

    It is an error if the hook attribute is missing or if any builtin has been
    hooked multiple times.

    If attribute verification is disabled, then these conditions are not
    checked. However, attribute parser errors will still be reported!

 -}
verifyHookAttribute
    :: KoreIndexedModule atts
    -> AttributesVerification atts
    -> Attributes
    -> Either (Error VerifyError) Hook
verifyHookAttribute
    indexedModule
    attributesVerification
    attributes
  = do
    hook@Hook { getHook } <- castError (parseAttributes attributes)
    case attributesVerification of
        DoNotVerifyAttributes -> return hook  -- caveat emptor
        VerifyAttributes _ -> do
            hookId <- maybe (koreFail "Missing hook attribute") return getHook
            -- Ensures that the builtin is hooked only once.
            -- The module is already indexed, so if it is hooked only once then
            -- it must be hooked here.
            _ <- resolveHook indexedModule hookId
            return hook
