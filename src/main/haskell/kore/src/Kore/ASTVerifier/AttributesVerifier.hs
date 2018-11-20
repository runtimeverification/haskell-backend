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
    , verifySortHookAttribute
    , verifySymbolHookAttribute
    , verifyNoHookAttribute
    , AttributesVerification (..)
    , parseAttributes
    ) where

import Data.Proxy
       ( Proxy )

import           Kore.AST.Common
import           Kore.AST.Kore
                 ( KorePattern, applyKorePattern )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Sentence
import           Kore.ASTVerifier.Error
import           Kore.Attribute.Hook
import qualified Kore.Attribute.Parser as Attribute.Parser
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )

{-| Whether we should verify attributes and, when verifying, the module with
declarations visible in these atributes. -}
data AttributesVerification atts
    = VerifyAttributes (Proxy atts)
    | DoNotVerifyAttributes

parseAttributes :: Attributes -> Either (Error VerifyError) Hook
parseAttributes = Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

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

{- | Verify that the @hook{}()@ attribute is present and well-formed.

    It is an error if any builtin has been hooked multiple times.

    If attribute verification is disabled, then 'emptyHook' is returned.

 -}
verifySortHookAttribute
    :: KoreIndexedModule atts
    -> AttributesVerification atts
    -> Attributes
    -> Either (Error VerifyError) Hook
verifySortHookAttribute _indexedModule =
    \case
        DoNotVerifyAttributes ->
            \_ -> return emptyHook
        VerifyAttributes _ ->
            \attributes -> parseAttributes attributes

{- | Verify that the @hook{}()@ attribute is present and well-formed.

    It is an error if any builtin has been hooked multiple times.

    If attribute verification is disabled, then 'emptyHook' is returned.

 -}
verifySymbolHookAttribute
    :: AttributesVerification atts
    -> Attributes
    -> Either (Error VerifyError) Hook
verifySymbolHookAttribute =
    \case
        DoNotVerifyAttributes ->
            -- Do not attempt to parse, verify, or return the hook attribute.
            \_ -> return emptyHook
        VerifyAttributes _ ->
            \attributes -> parseAttributes attributes

{- | Verify that the @hook{}()@ attribute is not present.

    It is an error if a non-@hooked@ declaration has a @hook@ attribute.

 -}
verifyNoHookAttribute
    :: AttributesVerification atts
    -> Attributes
    -> Either (Error VerifyError) ()
verifyNoHookAttribute =
    \case
        DoNotVerifyAttributes ->
            -- Do not verify anything.
            \_ -> return ()
        VerifyAttributes _ -> \attributes -> do
            Hook { getHook } <- castError (parseAttributes attributes)
            case getHook of
                Nothing ->
                    -- The hook attribute is (correctly) absent.
                    return ()
                Just _ -> do
                    koreFail "Unexpected 'hook' attribute"
