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

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Data.Functor.Foldable as Recursive
import Data.Proxy
    ( Proxy
    )

import Kore.ASTVerifier.Error
import Kore.Attribute.Hook
import qualified Kore.Attribute.Parser as Attribute.Parser
import Kore.Error
import Kore.Syntax.Definition
import Kore.Syntax.Pattern

{-| Whether we should verify attributes and, when verifying, the module with
declarations visible in these atributes. -}
data AttributesVerification declAtts axiomAtts
    = VerifyAttributes (Proxy declAtts) (Proxy axiomAtts)
    | DoNotVerifyAttributes

parseAttributes :: MonadError (Error VerifyError) m => Attributes -> m Hook
parseAttributes = Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

{-|'verifyAttributes' verifies the wellformedness of the given attributes.
-}
verifyAttributes
    :: MonadError (Error VerifyError) m
    => Attributes
    -> AttributesVerification declAtts axiomAtts
    -> m VerifySuccess
verifyAttributes
    (Attributes patterns)
    (VerifyAttributes _ _)
  = do
    withContext
        "attributes"
        (mapM_ (verifyAttributePattern . project) patterns)
    verifySuccess
  where
    project = Cofree.tailF . Recursive.project
verifyAttributes _ DoNotVerifyAttributes =
    verifySuccess

verifyAttributePattern
    :: MonadError (Error VerifyError) m
    => PatternF variable (Pattern variable annotation)
    -> m VerifySuccess
verifyAttributePattern pat =
    case pat of
        ApplicationF _ -> verifySuccess
        _ ->
            koreFail "Non-application attributes are not supported"

{- | Verify that the @hook{}()@ attribute is present and well-formed.

    It is an error if any builtin has been hooked multiple times.

    If attribute verification is disabled, then 'emptyHook' is returned.

 -}
verifySortHookAttribute
    :: MonadError (Error VerifyError) error
    => AttributesVerification declAtts axiomAtts
    -> Attributes
    -> error Hook
verifySortHookAttribute =
    \case
        DoNotVerifyAttributes ->
            \_ -> return emptyHook
        VerifyAttributes _ _ -> \attrs -> do
            hook <- parseAttributes attrs
            case getHook hook of
                Just _  -> return hook
                Nothing -> koreFail "missing hook attribute"

{- | Verify that the @hook{}()@ attribute is present and well-formed.

    It is an error if any builtin has been hooked multiple times.

    If attribute verification is disabled, then 'emptyHook' is returned.

 -}
verifySymbolHookAttribute
    :: MonadError (Error VerifyError) error
    => AttributesVerification declAtts axiomAtts
    -> Attributes
    -> error Hook
verifySymbolHookAttribute =
    \case
        DoNotVerifyAttributes ->
            -- Do not attempt to parse, verify, or return the hook attribute.
            \_ -> return emptyHook
        VerifyAttributes _ _ -> \attrs -> do
            hook <- parseAttributes attrs
            case getHook hook of
                Just _  -> return hook
                Nothing -> koreFail "missing hook attribute"

{- | Verify that the @hook{}()@ attribute is not present.

    It is an error if a non-@hooked@ declaration has a @hook@ attribute.

 -}
verifyNoHookAttribute
    :: MonadError (Error VerifyError) error
    => AttributesVerification declAtts axiomAtts
    -> Attributes
    -> error ()
verifyNoHookAttribute =
    \case
        DoNotVerifyAttributes ->
            -- Do not verify anything.
            \_ -> return ()
        VerifyAttributes _ _ -> \attributes -> do
            Hook { getHook } <- parseAttributes attributes
            case getHook of
                Nothing ->
                    -- The hook attribute is (correctly) absent.
                    return ()
                Just _ ->
                    koreFail "Unexpected 'hook' attribute"
