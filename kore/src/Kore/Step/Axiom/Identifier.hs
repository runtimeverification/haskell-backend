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

import Control.Applicative
    ( Alternative (..)
    )
import qualified Data.Functor.Foldable as Recursive
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import qualified Data.Text.Prettyprint.Doc as Doc
    ( parens
    , (<+>)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import qualified Kore.Builtin.External as Builtin
import Kore.Debug
import Kore.Internal.TermLike
    ( CofreeF (..)
    , InternalVariable
    , TermLike
    )
import qualified Kore.Syntax.Application as Syntax
import qualified Kore.Syntax.Ceil as Syntax
import qualified Kore.Syntax.Equals as Syntax
import qualified Kore.Syntax.Exists as Syntax
import Kore.Syntax.Id
    ( Id (..)
    )
import Kore.Syntax.PatternF
import Kore.Unparser
    ( unparse
    )

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
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic AxiomIdentifier

instance SOP.HasDatatypeInfo AxiomIdentifier

instance Debug AxiomIdentifier

instance Diff AxiomIdentifier

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
matchAxiomIdentifier
    :: InternalVariable variable
    => TermLike variable
    -> Maybe AxiomIdentifier
matchAxiomIdentifier = Recursive.fold matchWorker . Builtin.externalize
  where
    matchWorker (_ :< patternF) =
        case patternF of
            ApplicationF application ->
                pure (Application symbolId)
              where
                symbol = Syntax.applicationSymbolOrAlias application
                symbolId = Syntax.symbolOrAliasConstructor symbol
            CeilF ceil -> Ceil <$> Syntax.ceilChild ceil
            EqualsF equals ->
                Equals
                    <$> Syntax.equalsFirst equals
                    <*> Syntax.equalsSecond equals
            ExistsF exists -> Exists <$> Syntax.existsChild exists
            VariableF _ ->
                pure Variable
            _ -> empty
