{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

@Definition@ models a K definition (a main module with its transitive
imports) that has been verified and is optimised for the needs of the
simple rewriter matching pattern terms to rule LHS terms.

Axioms are stored in a lookup map according to the _index_ of their LHS,
and in groups of equal priority (descending order).

Symbols (and constructors) are stored in a lookup table by their name.
-}
module Booster.Definition.Base (
    module Booster.Definition.Base,
) where

import Control.DeepSeq (NFData)
import Data.ByteString.Char8 (ByteString)
import Data.Map.Strict as Map (Map, empty)
import Data.Set (Set)
import GHC.Generics qualified as GHC

import Booster.Definition.Attributes.Base
import Booster.Pattern.Base
import Booster.Pattern.Index (TermIndex)

{- | A Kore definition is constructed from a main module with its
   transitive imports.

All sentences are gathered together and their data stored in different
fields, depending on the sentence type.

A consistent import hierarchy and scoping is not guaranteed within the
data type, but rather by its construction from a @ParsedDefinition@.
-}
data KoreDefinition = KoreDefinition
    { attributes :: DefinitionAttributes
    , modules :: Map ByteString ModuleAttributes
    , sorts :: Map SortName (SortAttributes, Set SortName)
    , symbols :: Map SymbolName Symbol -- constructors and functions
    , aliases :: Map AliasName Alias
    , rewriteTheory :: Theory (RewriteRule "Rewrite")
    , functionEquations :: Theory (RewriteRule "Function")
    , simplifications :: Theory (RewriteRule "Simplification")
    , predicateSimplifications :: Theory PredicateEquation
    }
    deriving stock (Eq, Show, GHC.Generic)
    deriving anyclass (NFData)

-- | Axiom store, optimized for lookup by term-index and priority
type Theory axiomType = Map TermIndex (Map Priority [axiomType])

{- | The starting point for building up the definition. Could be
 'Monoid' instance if the attributes had a Default.
-}
emptyKoreDefinition :: DefinitionAttributes -> KoreDefinition
emptyKoreDefinition attributes =
    KoreDefinition
        { attributes
        , modules = Map.empty
        , sorts = Map.empty
        , symbols = Map.empty
        , aliases = Map.empty
        , rewriteTheory = Map.empty
        , functionEquations = Map.empty
        , simplifications = Map.empty
        , predicateSimplifications = Map.empty
        }

data RewriteRule (tag :: k) = RewriteRule
    { lhs, rhs :: Term
    , requires, ensures :: [Predicate]
    , attributes :: AxiomAttributes
    , computedAttributes :: ComputedAxiomAttributes
    , existentials :: Set Variable
    }
    deriving stock (Eq, Ord, Show, GHC.Generic)
    deriving anyclass (NFData)

type AliasName = ByteString

data Alias = Alias
    { name :: AliasName
    , params :: [Sort]
    , args :: [Variable]
    , rhs :: TermOrPredicate
    }
    deriving stock (Eq, Ord, Show, GHC.Generic)
    deriving anyclass (NFData)

data PredicateEquation = PredicateEquation
    { target :: Predicate
    , conditions :: [Predicate]
    , rhs :: [Predicate]
    , attributes :: AxiomAttributes
    , computedAttributes :: ComputedAxiomAttributes
    }
    deriving stock (Eq, Ord, Show, GHC.Generic)
    deriving anyclass (NFData)
