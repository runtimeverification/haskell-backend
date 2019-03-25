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

import Kore.AST.Common
       ( SymbolOrAlias (..) )
import Kore.AST.Identifier
       ( Id (..) )
import Kore.AST.Pure
       ( PurePattern )
import Kore.AST.Valid
       ( pattern App_, pattern Ceil_ )

{-| Identifer for the left-hand-side of axioms and for the terms with which
these can be identified.

The expectation is that an axiom can be applied to a term only if the
identifier of its left-hand-side is the same as the term's identifier.
-}
data AxiomIdentifier level
    = Application !(Id level)
    -- ^ Identifier for an application pattern whose symbol has the given id
    -- as name and which has no parameters.
    | Ceil !(AxiomIdentifier level)
    -- ^ Identifier for a ceil pattern whose child has the given identifier.
    deriving (Eq, Ord, Show)

{-|Given a pattern, returns its identifier, if any can be extracted.
Returns Nothing if it will not handle the current pattern.

Currently parameters of parameterized symbols are ignored.
-}
extract
    :: (Functor domain)
    => PurePattern level domain variable annotation
    -> Maybe (AxiomIdentifier level)
extract (App_ symbolOrAlias _children) =
    Just (Application (symbolOrAliasConstructor symbolOrAlias))
extract (Ceil_ _sort1 _sort2 (App_ symbolOrAlias _children)) =
    Just (Ceil (Application (symbolOrAliasConstructor symbolOrAlias)))
extract _ = Nothing
