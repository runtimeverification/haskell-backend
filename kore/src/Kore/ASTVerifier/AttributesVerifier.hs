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
    --, verifySymbolAttributes
    --, verifyAxiomAttributes
    --, verifySortAttributes
    , parseAttributes
    ) where

import qualified Control.Lens as Lens
import Data.Generics.Product
import Data.Function
    ((&)
    )
import Data.Bifunctor
import Kore.IndexedModule.MetadataTools as MetadataTools
import Prelude.Kore

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Data.Functor.Foldable as Recursive

import Kore.Attribute.Symbol
import Kore.ASTVerifier.Error
import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import Kore.Attribute.Hook
import qualified Kore.Attribute.Parser as Attribute.Parser
import Kore.Error
import Kore.Syntax.Application
    ( SymbolOrAlias (..)
    )
import Kore.Syntax.Definition
import qualified Kore.Internal.Symbol as Internal.Symbol
import Kore.Syntax.Pattern
import Kore.Attribute.Overload

parseAttributes :: MonadError (Error VerifyError) m => Attributes -> m Hook
parseAttributes = Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

{-|'verifyAttributes' verifies the wellformedness of the given attributes.
-}
verifyAttributes
    :: MonadError (Error VerifyError) m
    => Attributes
    -> m VerifySuccess
verifyAttributes (Attributes patterns)
  = do
    withContext
        "attributes"
        (mapM_ (verifyAttributePattern . project) patterns)
    verifySuccess
  where
    project = Cofree.tailF . Recursive.project

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
    => Attributes
    -> error Hook
verifySortHookAttribute attrs = do
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
    => Attributes
    -> error Hook
verifySymbolHookAttribute attrs = do
    hook <- parseAttributes attrs
    case getHook hook of
        Just _  -> return hook
        Nothing -> koreFail "missing hook attribute"

{- | Verify that the @hook{}()@ attribute is not present.

    It is an error if a non-@hooked@ declaration has a @hook@ attribute.

 -}
verifyNoHookAttribute
    :: MonadError (Error VerifyError) error
    => Attributes
    -> error ()
verifyNoHookAttribute attributes = do
    Hook { getHook } <- parseAttributes attributes
    case getHook of
        Nothing ->
            -- The hook attribute is (correctly) absent.
            return ()
        Just _ ->
            koreFail "Unexpected 'hook' attribute"


verifySymbolAttributes
    :: Attribute.Axiom SymbolOrAlias
    -> Attribute.Axiom Internal.Symbol.Symbol
verifySymbolAttributes axiom =
    axiom & field @"overload" Lens.%~ fmap toSymbol
  where
    toSymbol s = Internal.Symbol.Symbol
        { Internal.Symbol.symbolConstructor = sId
        , Internal.Symbol.symbolParams = symbolOrAliasParams s
        , Internal.Symbol.symbolSorts = undefined
        , Internal.Symbol.symbolAttributes = defaultSymbolAttributes
        }
      where
          sId = symbolOrAliasConstructor s

verifyAxiomAttributes :: a
verifyAxiomAttributes = undefined

verifySortAttributes :: a
verifySortAttributes = undefined