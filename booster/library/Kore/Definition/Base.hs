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
module Kore.Definition.Base (
    module Kore.Definition.Base,
) where

import Data.Map.Strict as Map (Map, empty)
import Data.Set (Set)
import Data.Text (Text)

import Kore.Definition.Attributes.Base
import Kore.Pattern.Base

{- | A Kore definition is constructed from a main module with its
   transitive imports.

All sentences are gathered together and their data stored in different
fields, depending on the sentence type.

A consistent import hierarchy and scoping is not guaranteed within the
data type, but rather by its construction from a @ParsedDefinition@.
-}
data KoreDefinition = KoreDefinition
    { attributes :: DefinitionAttributes
    , modules :: Map Text ModuleAttributes
    , sorts :: Map SortName (SortAttributes, Set SortName)
    , symbols :: Map SymbolName (SymbolAttributes, SymbolSort) -- constructors and functions
    , aliases :: Map AliasName Alias
    , rewriteTheory :: RewriteTheory
    }
    deriving (Eq, Show)

-- | Optimized for lookup by term-index
type RewriteTheory = Map TermIndex (Map Priority [RewriteRule])

-- | Sort information related to a symbol: result and argument sorts
data SymbolSort = SymbolSort
    { resultSort :: Sort
    , argSorts :: [Sort]
    }
    deriving stock (Eq, Show)

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
        }

data RewriteRule = RewriteRule
    { lhs :: Pattern
    , rhs :: Pattern
    , attributes :: AxiomAttributes
    }
    deriving stock (Eq, Ord, Show)

extractPriority :: RewriteRule -> Priority
extractPriority RewriteRule{attributes} = priority attributes

type AliasName = Text

data Alias = Alias
    { name :: AliasName
    , params :: [Sort]
    , args :: [Variable]
    , rhs :: TermOrPredicate
    }
    deriving stock (Eq, Show)
