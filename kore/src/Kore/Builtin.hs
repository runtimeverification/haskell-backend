{- |
Module      : Kore.Builtin
Description : Built-in sorts and symbols
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified.

@
    import qualified Kore.Builtin as Builtin
@
-}
module Kore.Builtin (
    Builtin.Verifiers (..),
    Builtin.ApplicationVerifiers,
    BuiltinAndAxiomSimplifier,
    Builtin.SymbolVerifier (..),
    Builtin.SortVerifier (..),
    Builtin.ApplicationVerifier (..),
    Builtin.SymbolKey (..),
    Builtin.PatternVerifierHook (..),
    Builtin.lookupApplicationVerifier,
    Builtin.sortDeclVerifier,
    Builtin.symbolVerifier,
    koreVerifiers,
    koreEvaluators,
    evaluators,
    internalize,
) where

import Data.Functor.Foldable qualified as Recursive
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Text (
    Text,
 )
import Kore.Attribute.Hook (
    Hook (..),
 )
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Builtin.Bool qualified as Bool
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.Endianness qualified as Endianness
import Kore.Builtin.Inj qualified as Inj
import Kore.Builtin.Int qualified as Int
import Kore.Builtin.InternalBytes qualified as InternalBytes
import Kore.Builtin.KEqual qualified as KEqual
import Kore.Builtin.Kreflection qualified as Kreflection
import Kore.Builtin.Krypto qualified as Krypto
import Kore.Builtin.List qualified as List
import Kore.Builtin.Map qualified as Map
import Kore.Builtin.Set qualified as Set
import Kore.Builtin.Signedness qualified as Signedness
import Kore.Builtin.String qualified as String
import Kore.IndexedModule.IndexedModule (
    IndexedModuleSyntax (..),
    VerifiedModuleSyntax,
 )
import Kore.IndexedModule.IndexedModule qualified as IndexedModule
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.Axiom.Identifier (
    AxiomIdentifier,
 )
import Kore.Rewrite.Axiom.Identifier qualified as AxiomIdentifier (
    AxiomIdentifier (..),
 )
import Kore.Simplify.Simplify (
    BuiltinAndAxiomSimplifier,
 )
import Prelude.Kore

{- | Verifiers for Kore builtin sorts.

  If you aren't sure which verifiers you need, use these.
-}
koreVerifiers :: Builtin.Verifiers
koreVerifiers =
    mempty
        <> Bool.verifiers
        <> Endianness.verifiers
        <> Inj.verifiers
        <> Int.verifiers
        <> InternalBytes.verifiers
        <> KEqual.verifiers
        <> Krypto.verifiers
        <> List.verifiers
        <> Map.verifiers
        <> Set.verifiers
        <> Signedness.verifiers
        <> String.verifiers
        <> Kreflection.verifiers

{- | Construct an evaluation context for Kore builtin functions.

  Returns a map from symbol identifiers to builtin functions used for function
  evaluation in the context of the given module.

  See also: 'Data.Step.Step.step'
-}
koreEvaluators ::
    -- | Module under which evaluation takes place
    VerifiedModuleSyntax StepperAttributes ->
    Map AxiomIdentifier BuiltinAndAxiomSimplifier
koreEvaluators = evaluators builtins
  where
    builtins :: Map Text BuiltinAndAxiomSimplifier
    builtins =
        Map.unions
            [ Bool.builtinFunctions
            , Int.builtinFunctions
            , KEqual.builtinFunctions
            , List.builtinFunctions
            , Map.builtinFunctions
            , Set.builtinFunctions
            , String.builtinFunctions
            , Krypto.builtinFunctions
            , InternalBytes.builtinFunctions
            ]

{- | Construct an evaluation context for the given builtin functions.

  Returns a map from symbol identifiers to builtin functions used for function
  evaluation in the context of the given module.

  See also: 'Data.Step.Step.step', 'koreEvaluators'
-}
evaluators ::
    -- | Builtin functions indexed by name
    Map Text BuiltinAndAxiomSimplifier ->
    -- | Module under which evaluation takes place
    VerifiedModuleSyntax StepperAttributes ->
    Map AxiomIdentifier BuiltinAndAxiomSimplifier
evaluators builtins indexedModule =
    Map.mapMaybe
        lookupBuiltins
        ( Map.mapKeys
            AxiomIdentifier.Application
            (hookedSymbolAttributes indexedModule)
        )
  where
    hookedSymbolAttributes ::
        VerifiedModuleSyntax StepperAttributes ->
        Map Id StepperAttributes
    hookedSymbolAttributes im =
        Map.union
            (justAttributes <$> IndexedModule.hookedObjectSymbolSentences im)
            ( Map.unions
                (importHookedSymbolAttributes <$> indexedModuleImportsSyntax im)
            )
      where
        justAttributes (attrs, _) = attrs

    importHookedSymbolAttributes ::
        (a, b, VerifiedModuleSyntax StepperAttributes) ->
        Map Id StepperAttributes
    importHookedSymbolAttributes (_, _, im) = hookedSymbolAttributes im

    lookupBuiltins :: StepperAttributes -> Maybe BuiltinAndAxiomSimplifier
    lookupBuiltins Attribute.Symbol{Attribute.hook = Hook{getHook}} =
        do
            name <- getHook
            Map.lookup name builtins

{- | Convert a 'TermLike' to its internal representation.

@internalize@ modifies the term recursively from the bottom up, so any internal
representations are fully normalized.
-}
internalize ::
    InternalVariable variable =>
    SmtMetadataTools Attribute.Symbol ->
    TermLike variable ->
    TermLike variable
internalize tools =
    Recursive.fold (internalize1 . Recursive.embed)
  where
    internalize1 =
        List.internalize tools
            . Map.internalize tools
            . Set.internalize tools
            . InternalBytes.internalize
