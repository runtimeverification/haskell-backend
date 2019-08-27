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
    , extract
    ) where

import qualified Data.Functor.Foldable as Recursive

import           Kore.Internal.TermLike hiding
                 ( Application, Ceil, extract )
import qualified Kore.Syntax.Application as Syntax
import qualified Kore.Syntax.Ceil as Syntax
import           Kore.Syntax.Id
                 ( Id (..) )

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
    deriving (Eq, Ord, Show)

{-|Given a pattern, returns its identifier, if any can be extracted.
Returns Nothing if it will not handle the current pattern.

Currently parameters of parameterized symbols are ignored.
-}
-- TODO (thomas.tuegel): Rename this to avoid conflicting with Comonad.
extract :: TermLike variable -> Maybe AxiomIdentifier
extract (Recursive.project -> _ :< termLikeF)
  | ApplySymbolF applySymbolF <- termLikeF = extractApplication applySymbolF
  | CeilF Syntax.Ceil { ceilChild } <- termLikeF
  , _ :< ApplySymbolF applySymbolF <- Recursive.project ceilChild
  =
    Ceil <$> extractApplication applySymbolF
  | otherwise = Nothing
  where
    extractApplication Syntax.Application { applicationSymbolOrAlias } =
      Just $ Application $ symbolConstructor applicationSymbolOrAlias
