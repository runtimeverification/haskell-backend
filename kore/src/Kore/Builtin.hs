{- |
Module      : Kore.Builtin
Description : Built-in sorts and symbols
Copyright   : (c) Runtime Verification, 2018
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

import qualified Data.Functor.Foldable as Recursive
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import Kore.Attribute.Hook (
    Hook (..),
 )
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Endianness as Endianness
import qualified Kore.Builtin.Inj as Inj
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.InternalBytes as InternalBytes
import qualified Kore.Builtin.KEqual as KEqual
import qualified Kore.Builtin.Kreflection as Kreflection
import qualified Kore.Builtin.Krypto as Krypto
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Set as Set
import qualified Kore.Builtin.Signedness as Signedness
import qualified Kore.Builtin.String as String
import Kore.IndexedModule.IndexedModule (
    IndexedModule (..),
    VerifiedModule,
 )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.TermLike
import Kore.Step.Axiom.Identifier (
    AxiomIdentifier,
 )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier (
    AxiomIdentifier (..),
 )
import Kore.Step.Simplification.Simplify (
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
    VerifiedModule StepperAttributes ->
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
    VerifiedModule StepperAttributes ->
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
        VerifiedModule StepperAttributes ->
        Map Id StepperAttributes
    hookedSymbolAttributes im =
        Map.union
            (justAttributes <$> IndexedModule.hookedObjectSymbolSentences im)
            ( Map.unions
                (importHookedSymbolAttributes <$> indexedModuleImports im)
            )
      where
        justAttributes (attrs, _) = attrs

    importHookedSymbolAttributes ::
        (a, b, VerifiedModule StepperAttributes) ->
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
