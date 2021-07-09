{- |
Module      : Kore.Step.Axiom.Identifier
Description : Data structures and manipulation helpers used for axiom
              evaluation identifiers.
              The expectation is that an axiom can be applied to a term
              only if the identifier of its left-hand-side is the same
              as the term's identifier.
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
This module is intended to be imported qualified:
@
import Kore.Step.Axiom.Identifier ( AxiomIdentifier )
import Kore.Step.Axiom.Identifier as AxiomIdentifier
@
-}
module Kore.Step.Axiom.Identifier (
    AxiomIdentifier (..),
    matchAxiomIdentifier,
) where

import Data.Functor.Const (
    Const (..),
 )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Sequence as Seq
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Builtin.Endianness.Endianness as Endianness
import qualified Kore.Builtin.Signedness.Signedness as Signedness
import Kore.Debug
import qualified Kore.Internal.Alias as Alias
import qualified Kore.Internal.Inj as Inj
import Kore.Internal.InternalList
import Kore.Internal.InternalSet
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike (
    TermLike,
    TermLikeF (..),
 )
import qualified Kore.Syntax.Application as Syntax
import qualified Kore.Syntax.Ceil as Syntax
import qualified Kore.Syntax.Equals as Syntax
import qualified Kore.Syntax.Exists as Syntax
import Kore.Syntax.Id (
    Id (..),
 )
import Kore.Unparser (
    unparse,
 )
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

{- | Identifer for the left-hand-side of axioms and for the terms with which
these can be identified.

The expectation is that an axiom can be applied to a term only if the
identifier of its left-hand-side is the same as the term's identifier.
-}
data AxiomIdentifier
    = -- | An application pattern with the given symbol identifier.
      Application !Id
    | -- | A @\\ceil@ pattern with the given child.
      Ceil !AxiomIdentifier
    | -- | An @\\equals@ pattern with the given children.
      Equals !AxiomIdentifier !AxiomIdentifier
    | -- | An @\\exists@ pattern with the given child.
      Exists !AxiomIdentifier
    | -- | Any variable pattern.
      Variable
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Pretty AxiomIdentifier where
    pretty (Application name) = unparse name
    pretty (Ceil axiomIdentifier) =
        "\\ceil" <> Pretty.parens (pretty axiomIdentifier)
    pretty (Equals first second) =
        "\\equals"
            <> Pretty.parens
                (pretty first Pretty.<+> "," Pretty.<+> pretty second)
    pretty (Exists axiomIdentifier) =
        "\\exists" <> Pretty.parens (pretty axiomIdentifier)
    pretty Variable = "_"

{- | Match 'TermLike' pattern to determine its 'AxiomIdentifier'.

Returns 'Nothing' if the 'TermLike' does not conform to one of the structures we
recognize.
-}
matchAxiomIdentifier ::
    TermLike variable ->
    Maybe AxiomIdentifier
matchAxiomIdentifier = Recursive.fold matchWorker
  where
    matchWorker (_ :< termLikeF) =
        case termLikeF of
            ApplyAliasF application -> mkAliasId application
            ApplySymbolF application -> mkAppId application
            CeilF ceil -> Ceil <$> Syntax.ceilChild ceil
            EqualsF equals ->
                Equals
                    <$> Syntax.equalsFirst equals
                    <*> Syntax.equalsSecond equals
            ExistsF exists -> Exists <$> Syntax.existsChild exists
            VariableF _ ->
                pure Variable
            EndiannessF endiannessF ->
                mkAppId $
                    Endianness.toApplication $ getConst endiannessF
            SignednessF signednessF ->
                mkAppId $
                    Signedness.toApplication $ getConst signednessF
            InjF inj -> mkAppId $ Inj.toApplication inj
            InternalListF internalList -> listToId internalList
            InternalSetF internalSet -> mapToId internalSet
            InternalMapF internalMap -> setToId internalMap
            _ -> empty

    listToId internalList
        | Seq.null list = pure $ Application $ symbolToId unitSymbol
        | Seq.length list == 1 = pure $ Application $ symbolToId elementSymbol
        | otherwise = pure $ Application $ symbolToId concatSymbol
      where
        InternalList{internalListChild = list} = internalList
        InternalList{internalListUnit = unitSymbol} = internalList
        InternalList{internalListElement = elementSymbol} = internalList
        InternalList{internalListConcat = concatSymbol} = internalList

    mapToId internalMap =
        acToId
            unitSymbol
            elementSymbol
            concatSymbol
            elementsWithVariables
            (HashMap.toList concreteElements)
            opaque
      where
        InternalAc{builtinAcChild} = internalMap
        InternalAc{builtinAcUnit = unitSymbol} = internalMap
        InternalAc{builtinAcElement = elementSymbol} = internalMap
        InternalAc{builtinAcConcat = concatSymbol} = internalMap

        normalizedAc = unwrapAc builtinAcChild

        NormalizedAc{elementsWithVariables} = normalizedAc
        NormalizedAc{concreteElements} = normalizedAc
        NormalizedAc{opaque} = normalizedAc

    setToId internalSet =
        acToId
            unitSymbol
            elementSymbol
            concatSymbol
            elementsWithVariables
            (HashMap.toList concreteElements)
            opaque
      where
        InternalAc{builtinAcChild} = internalSet
        InternalAc{builtinAcUnit = unitSymbol} = internalSet
        InternalAc{builtinAcElement = elementSymbol} = internalSet
        InternalAc{builtinAcConcat = concatSymbol} = internalSet

        normalizedAc = unwrapAc builtinAcChild

        NormalizedAc{elementsWithVariables} = normalizedAc
        NormalizedAc{concreteElements} = normalizedAc
        NormalizedAc{opaque} = normalizedAc

    acToId unitSymbol _ _ [] [] [] = pure $ Application $ symbolToId unitSymbol
    acToId _ elementSymbol _ [_] [] [] = pure $ Application $ symbolToId elementSymbol
    acToId _ elementSymbol _ [] [_] [] = pure $ Application $ symbolToId elementSymbol
    acToId _ _ _ [] [] [opaque] = opaque
    acToId _ _ concatSymbol _ _ _ = pure $ Application $ symbolToId concatSymbol

    mkAppId = pure . Application . symbolToId . Syntax.applicationSymbolOrAlias
    mkAliasId = pure . Application . aliasToId . Syntax.applicationSymbolOrAlias
    symbolToId = Syntax.symbolOrAliasConstructor . Symbol.toSymbolOrAlias
    aliasToId = Syntax.symbolOrAliasConstructor . Alias.toSymbolOrAlias
