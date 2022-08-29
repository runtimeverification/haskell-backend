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
    internalize,
) where

import Data.Functor.Foldable qualified as Recursive
import Data.Text (
    Text,
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
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify
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

  Given the name of a hook, returns the builtin function used for function
  evaluation in the context of the given module.

  See also: 'Data.Step.Step.step'
-}
koreEvaluators ::
    Text ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    Maybe (Simplifier (AttemptedAxiom RewritingVariableName))
koreEvaluators key termLike sideCondition =
    asum $ map (\evaluator -> evaluator termLike sideCondition)
        [ Bool.builtinFunctions key
        , Int.builtinFunctions key
        , KEqual.builtinFunctions key
        , List.builtinFunctions key
        , Map.builtinFunctions key
        , Set.builtinFunctions key
        , String.builtinFunctions key
        , Krypto.builtinFunctions key
        , InternalBytes.builtinFunctions key
        ]
{-# INLINE koreEvaluators #-}

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
