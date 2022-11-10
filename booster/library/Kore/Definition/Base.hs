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

{- | Index data allowing for a quick lookup of potential axioms.

A @Term@ is indexed by inspecting the top term component of the
head of the K cell. Only constructor and (other) symbol
applications are indexed, all other terms have index @Anything@.

In particular, function applications are treated as opaque, like
variables.

Also, non-free constructors won't get any index, any rules headed by
those can be ignored.

Rather than making the term indexing function partial, we introduce a
unique bottom element @None@ to the index type (to make it a lattice).
This can then handle @AndTerm@ by indexing both arguments and
combining them.

NB we should not derive an 'Ord' instance since it would not reflect
the fact that different symbols (and likewise different constructors)
are incompatible.
-}
data TermIndex
    = None -- bottom element
    | Symbol SymbolName
    | Anything -- top element
    -- should we have  | Value Sort ?? (see Term type)
    deriving (Eq, Show)

-- | Combines two indexes (an "infimum" function on the index lattice)
combine :: TermIndex -> TermIndex -> TermIndex
combine None _ = None
combine _ None = None
combine x Anything = x
combine Anything x = x
combine s@(Symbol s1) (Symbol s2)
    | s1 == s2 = s
--     | otherwise = None -- redundant
combine _ _ = None -- incompatible indexes

----------------------------------------

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
    , sorts :: Map SortName SortAttributes -- TODO store a lattice of subsorts?
    , symbols :: Map SymbolName (SymbolAttributes, SymbolSort) -- constructors and functions
    , axioms :: Map TermIndex [Set Axiom] -- grouped by decreasing priority
    }
    deriving (Eq, Show)

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
        , axioms = Map.empty
        }

data Axiom = Axiom
    { lhs :: Pattern
    , rhs :: Pattern
    , attributes :: AxiomAttributes
    }
    deriving (Eq, Show)
