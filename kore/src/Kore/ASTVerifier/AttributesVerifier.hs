{- |
Module      : Kore.ASTVerifier.AttributesVerifier
Description : Tools for verifying the wellformedness of Kore 'Attributes'.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.ASTVerifier.AttributesVerifier (
    verifyAttributes,
    verifySortHookAttribute,
    verifySymbolHookAttribute,
    verifyNoHookAttribute,
    verifySymbolAttributes,
    verifyAxiomAttributes,
    verifySortAttributes,
    parseAttributes,
) where

import qualified Control.Comonad.Trans.Cofree as Cofree
import qualified Control.Lens as Lens
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
import Kore.AST.AstWithLocation (
    locationFromAst,
 )
import Kore.ASTVerifier.Error
import qualified Kore.Attribute.Axiom as Attribute (
    Axiom,
    sourceLocation,
 )
import Kore.Attribute.Hook
import Kore.Attribute.Overload (
    Overload (..),
 )
import qualified Kore.Attribute.Parser as Attribute.Parser
import Kore.Attribute.Sort
import Kore.Attribute.Sort.HasDomainValues
import Kore.Attribute.Subsort as Subsort
import qualified Kore.Attribute.Symbol as Attribute.Symbol
import Kore.Error
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers
import Kore.Internal.ApplicationSorts (
    symbolOrAliasSorts,
 )
import qualified Kore.Internal.Symbol as Internal.Symbol
import Kore.Syntax.Application (
    SymbolOrAlias (..),
 )
import Kore.Syntax.Definition
import Kore.Syntax.Id (
    prettyPrintAstLocation,
 )
import Kore.Syntax.Pattern
import Kore.Syntax.Variable (
    VariableName (..),
 )
import Kore.Unparser (
    unparse,
 )
import qualified Kore.Verified as Verified
import Prelude.Kore
import Pretty

parseAttributes :: MonadError (Error VerifyError) m => Attributes -> m Hook
parseAttributes = Attribute.Parser.liftParser . Attribute.Parser.parseAttributes

-- |'verifyAttributes' verifies the wellformedness of the given attributes.
verifyAttributes ::
    MonadError (Error VerifyError) m =>
    Attributes ->
    m VerifySuccess
verifyAttributes (Attributes patterns) =
    do
        withContext
            "attributes"
            (mapM_ (verifyAttributePattern . project) patterns)
        verifySuccess
  where
    project = Cofree.tailF . Recursive.project

verifyAttributePattern ::
    MonadError (Error VerifyError) m =>
    PatternF variable (Pattern variable annotation) ->
    m VerifySuccess
verifyAttributePattern pat =
    case pat of
        ApplicationF _ -> verifySuccess
        _ ->
            koreFail "Non-application attributes are not supported"

{- | Verify that the @hook{}()@ attribute is present and well-formed.

    It is an error if any builtin has been hooked multiple times.

    If attribute verification is disabled, then 'emptyHook' is returned.
-}
verifySortHookAttribute ::
    MonadError (Error VerifyError) error =>
    Attributes ->
    error Hook
verifySortHookAttribute attrs = do
    hook <- parseAttributes attrs
    case getHook hook of
        Just _ -> return hook
        Nothing -> koreFail "missing hook attribute"

{- | Verify that the @hook{}()@ attribute is present and well-formed.

    It is an error if any builtin has been hooked multiple times.

    If attribute verification is disabled, then 'emptyHook' is returned.
-}
verifySymbolHookAttribute ::
    MonadError (Error VerifyError) error =>
    Attributes ->
    error Hook
verifySymbolHookAttribute attrs = do
    hook <- parseAttributes attrs
    case getHook hook of
        Just _ -> return hook
        Nothing -> koreFail "missing hook attribute"

{- | Verify that the @hook{}()@ attribute is not present.

    It is an error if a non-@hooked@ declaration has a @hook@ attribute.
-}
verifyNoHookAttribute ::
    MonadError (Error VerifyError) error =>
    Attributes ->
    error ()
verifyNoHookAttribute attributes = do
    Hook{getHook} <- parseAttributes attributes
    case getHook of
        Nothing ->
            -- The hook attribute is (correctly) absent.
            return ()
        Just _ ->
            koreFail "Unexpected 'hook' attribute"

verifyNoHookedSupersort ::
    MonadError (Error VerifyError) error =>
    IndexedModule Verified.Pattern Attribute.Symbol.Symbol attrs ->
    Attribute.Axiom SymbolOrAlias VariableName ->
    [Subsort.Subsort] ->
    error ()
verifyNoHookedSupersort indexedModule axiom subsorts = do
    let isHooked =
            getHasDomainValues . hasDomainValues
                . getSortAttributes indexedModule
                . Subsort.supersort
        hookedSubsort = find isHooked subsorts
    for_ hookedSubsort $ \sort ->
        koreFail . unlines $
            [ "Hooked sorts may not have subsorts."
            , "Hooked sort:"
            , show . unparse $ Subsort.supersort sort
            , "Its subsort:"
            , show . unparse $ Subsort.subsort sort
            , "Location in the Kore file:"
            , show . prettyPrintAstLocation $
                locationFromAst (Subsort.supersort sort)
            , "Location in the original K file: "
            , show . pretty $ Attribute.sourceLocation axiom
            ]

verifyAxiomAttributes ::
    forall error attrs.
    MonadError (Error VerifyError) error =>
    IndexedModule Verified.Pattern Attribute.Symbol.Symbol attrs ->
    Attribute.Axiom SymbolOrAlias VariableName ->
    error (Attribute.Axiom Internal.Symbol.Symbol VariableName)
verifyAxiomAttributes indexedModule axiom = do
    let overload = axiom Lens.^. field @"overload"
        subsorts = getSubsorts (axiom Lens.^. field @"subsorts")
    verifyNoHookedSupersort indexedModule axiom subsorts
    case getOverload overload of
        Nothing -> do
            let newOverload = Overload Nothing
            return (axiom & field @"overload" Lens..~ newOverload)
        Just (symbolOrAlias1, symbolOrAlias2) -> do
            symbol1 <- toSymbol symbolOrAlias1
            symbol2 <- toSymbol symbolOrAlias2
            let newOverload = Overload $ Just (symbol1, symbol2)
            return (axiom & field @"overload" Lens..~ newOverload)
  where
    toSymbol :: SymbolOrAlias -> error Internal.Symbol.Symbol
    toSymbol symbolOrAlias = do
        (symbolAttributes, decl) <-
            resolveSymbol indexedModule symbolConstructor
        symbolSorts <-
            symbolOrAliasSorts (symbolOrAliasParams symbolOrAlias) decl
        let symbol =
                Internal.Symbol.Symbol
                    { symbolConstructor
                    , symbolParams
                    , symbolAttributes
                    , symbolSorts
                    }
        return symbol
      where
        symbolConstructor = symbolOrAliasConstructor symbolOrAlias
        symbolParams = symbolOrAliasParams symbolOrAlias

verifySymbolAttributes ::
    forall error a.
    MonadError (Error VerifyError) error =>
    IndexedModule Verified.Pattern Attribute.Symbol.Symbol a ->
    Attribute.Symbol.Symbol ->
    error Attribute.Symbol.Symbol
verifySymbolAttributes _ attrs = return attrs

verifySortAttributes ::
    forall error a.
    MonadError (Error VerifyError) error =>
    IndexedModule Verified.Pattern Attribute.Symbol.Symbol a ->
    Attribute.Symbol.Symbol ->
    error Attribute.Symbol.Symbol
verifySortAttributes _ attrs = return attrs
