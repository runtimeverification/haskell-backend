{-|
Module      : Kore.Step.Axiom.Identifier
Description : Data structures and manipulation helpers used for axiom
              evaluation identifiers.

              The expectation is that an axiom can be applied to a term
              only if the identifier of its left-hand-side is the same
              as the term's identifier.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified:
@
import Kore.Step.Axiom.Identifier ( AxiomIdentifier )
import Kore.Step.Axiom.Identifier as AxiomIdentifier
@
-}

module Kore.Step.Axiom.Identifier
    ( AxiomIdentifier (..)
    , matchAxiomIdentifier
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Data.Functor.Foldable as Recursive
import           Data.Text.Prettyprint.Doc
                 ( Pretty (..) )
import qualified Data.Text.Prettyprint.Doc as Doc
                 ( parens, (<+>) )

import           Kore.Internal.TermLike
                 ( CofreeF (..), TermLike )
import qualified Kore.Internal.TermLike as TermLike
import           Kore.Syntax.Id
                 ( Id (..) )
import           Kore.Unparser
                 ( unparse )

{-| Identifer for the left-hand-side of axioms and for the terms with which
these can be identified.

The expectation is that an axiom can be applied to a term only if the
identifier of its left-hand-side is the same as the term's identifier.
-}
data AxiomIdentifier
    = Application !Id
    -- ^ An application pattern with the given symbol identifier.
    | Ceil !AxiomIdentifier
    -- ^ A @\\ceil@ pattern with the given child.
    | Equals !AxiomIdentifier !AxiomIdentifier
    -- ^ An @\\equals@ pattern with the given children.
    | Exists !AxiomIdentifier
    -- ^ An @\\exists@ pattern with the given child.
    | Variable
    -- ^ Any variable pattern.
    deriving (Eq, Ord, Show)

instance Pretty AxiomIdentifier where
    pretty (Application name) = unparse name
    pretty (Ceil axiomIdentifier) =
        "ceil" Doc.<+> Doc.parens (pretty axiomIdentifier)
    pretty (Equals first second) =
        "equals"
        Doc.<+> Doc.parens
            (pretty first Doc.<+> "," Doc.<+> pretty second)
    pretty (Exists axiomIdentifier) =
        "exists" Doc.<+> Doc.parens (pretty axiomIdentifier)
    pretty Variable = "variable"

{- | Match 'TermLike' pattern to determine its 'AxiomIdentifier'.

Returns 'Nothing' if the 'TermLike' does not conform to one of the structures we
recognize.

 -}
matchAxiomIdentifier :: TermLike variable -> Maybe AxiomIdentifier
matchAxiomIdentifier = Recursive.fold matchWorker
  where
    matchWorker (_ :< termLikeF) =
        case termLikeF of
            TermLike.ApplySymbolF application ->
                pure (Application symbolId)
              where
                symbol = TermLike.applicationSymbolOrAlias application
                symbolId = TermLike.symbolConstructor symbol
            TermLike.CeilF ceil ->
                Ceil <$> TermLike.ceilChild ceil
            TermLike.EqualsF equals ->
                Equals
                    <$> TermLike.equalsFirst equals
                    <*> TermLike.equalsSecond equals
            TermLike.ExistsF exists ->
                Exists <$> TermLike.existsChild exists
            TermLike.VariableF _ ->
                pure Variable
            _ -> empty
