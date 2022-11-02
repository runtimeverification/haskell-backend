{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}

module Kore.Pattern.Base
  where

import Data.ByteString (ByteString)
import Data.Text (Text)

-- Currently these are draft types from
-- https://github.com/runtimeverification/haskell-backend/issues/3349

data Term
    = AndTerm Sort Term Term  -- used in #as patterns
    | SymbolApplication Sort [Sort] SymbolName [Term]
    | DomainValue Sort Term
    | StringLiteral String
    | BuiltinInt Int
    | BuiltinBool Bool
    | BuiltinBytes ByteString
    | BuiltinString String
    | BuiltinList [Term]
    | BuiltinMap [(Term, Term)]
    | BuiltinSet [(Term, ())]
    | ElementVariable Sort VarName
    | SetVariable Sort VarName  -- debatable if we will ever need this or not, AFAIK they are only used for #Ceil simplification rules
    | Inj Sort Sort Term
    deriving stock (Eq, Ord, Show)

-- Notice that Predicates don't have sorts
data Predicate
    = AndPredicate Predicate Predicate
    | Bottom
    | Ceil Term
    | EqualsTerm Sort Term Term
    | EqualsPredicate Predicate Predicate  -- I remember running into this one a few times, but I'm not sure if it was an integration test or a unit test
    | Exists VarName Predicate
    | Forall VarName Predicate -- do we need forall?
    | Iff Predicate Predicate
    | Implies Predicate Predicate
    | In Sort Term Term
    | Not Predicate
    | Or Predicate Predicate
    | Top
    deriving stock (Eq, Ord, Show)

data Pattern
    = Pattern
      { term :: Term
      , constraints :: [Predicate]
      }
    deriving stock (Eq, Ord, Show)

type VarName = Text
type SymbolName = Text
type SortName = Text

data Sort
    = SortApp SymbolName [Sort]
    | SortVar VarName
    | Builtin BuiltinSort
    deriving stock (Eq, Ord, Show)

data BuiltinSort
    = SortInt
    | SortBool
    | SortBytes
    | SortString
    | SortList
    | SortMap
    | SortSet
    deriving (Eq, Ord, Show)
