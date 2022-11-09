{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Base (
    -- export everything, modules above can re-export only type names
    module Kore.Pattern.Base,
) where

import Data.Text (Text)

{- | A term consists of an AST of constructors and function calls, as
   well as domain values (tokens and built-in types) and (element)
   variables.
   This is anything that can be part of a K configuration.

   Deliberately kept simple in this codebase (leaving out built-in
   types and containers).
-}
data Term
    = AndTerm Sort Term Term -- used in #as patterns
    | SymbolApplication Sort [Sort] SymbolName [Term]
    | DomainValue Sort Term
    | Var Variable
    deriving stock (Eq, Ord, Show)

{- | A predicate describes constraints on terms. It will always evaluate
   to 'Top' or 'Bottom'. Notice that 'Predicate's don't have a sort.
-}
data Predicate
    = AndPredicate Predicate Predicate
    | Bottom
    | Ceil Term
    | EqualsTerm Sort Term Term
    | EqualsPredicate Predicate Predicate -- I remember running into this one a few times, but I'm not sure if it was an integration test or a unit test
    | Exists VarName Predicate
    | Forall VarName Predicate -- do we need forall?
    | Iff Predicate Predicate
    | Implies Predicate Predicate
    | In Sort Term Term
    | Not Predicate
    | Or Predicate Predicate
    | Top
    deriving stock (Eq, Ord, Show)

-- | A term (configuration) constrained by a number of predicates.
data Pattern = Pattern
    { term :: Term
    , constraints :: [Predicate]
    }
    deriving stock (Eq, Ord, Show)

type VarName = Text
type SymbolName = Text
type SortName = Text

{- | A term has a particular 'Sort', which is part of a definition, and
  sorts can be subsorts of other sorts (represented in the definition).
-}
data Sort
    = -- | sort constructor, potentially with arguments
      SortApp SortName [Sort]
    | -- | sort variable (symbolic)
      SortVar VarName
    deriving stock (Eq, Ord, Show)

-- | A variable for symbolic execution or for terms in a rule.
data Variable = Variable
    { variableSort :: Sort
    , variableName :: VarName
    }
    deriving (Eq, Ord, Show)
