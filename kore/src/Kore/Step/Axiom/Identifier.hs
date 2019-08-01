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

import           Kore.Internal.TermLike
                 ( CofreeF (..), TermLike, TermLikeF )
import qualified Kore.Internal.TermLike as TermLike
import           Kore.Syntax.Id

{-| Identifer for the left-hand-side of axioms and for the terms with which
these can be identified.

The expectation is that an axiom can be applied to a term only if the
identifier of its left-hand-side is the same as the term's identifier.
-}
data AxiomIdentifier
    = Application !Id
    -- ^ Identifier for an application pattern whose symbol has the given id
    -- as name and which has no parameters.
    | Ceil !AxiomIdentifier
    -- ^ Identifier for a ceil pattern whose child has the given identifier.
    | Variable
    deriving (Eq, Ord, Show)

matchApplySymbol
    :: TermLikeF variable (Maybe AxiomIdentifier)
    -> Maybe AxiomIdentifier
matchApplySymbol (TermLike.ApplySymbolF application) =
    Just (Application symbolId)
  where
    symbolId =
        TermLike.symbolConstructor
        $ TermLike.applicationSymbolOrAlias application
matchApplySymbol _ = Nothing

matchCeil
    :: TermLikeF variable (Maybe AxiomIdentifier)
    -> Maybe AxiomIdentifier
matchCeil (TermLike.CeilF ceil) = Ceil <$> TermLike.ceilChild ceil
matchCeil _ = Nothing

matchVariable
    :: TermLikeF variable (Maybe AxiomIdentifier)
    -> Maybe AxiomIdentifier
matchVariable (TermLike.VariableF _) = Just Variable
matchVariable _ = Nothing

{- | Match 'TermLike' pattern to determine its 'AxiomIdentifier'.

Returns 'Nothing' if the 'TermLike' does not conform to one of the structures we
recognize.

 -}
matchAxiomIdentifier :: TermLike variable -> Maybe AxiomIdentifier
matchAxiomIdentifier = Recursive.fold matchers
  where
    matchers (_ :< termLikeF) =
            matchApplySymbol termLikeF
        <|> matchCeil        termLikeF
        <|> matchVariable    termLikeF
