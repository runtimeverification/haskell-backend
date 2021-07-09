{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Rewriting.UnifyingRule (
    UnifyingRule (..),
    InstantiationFailure (..),
    Renaming,
) where

import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
 )
import Kore.Syntax.Variable
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

type Renaming variable =
    Map (SomeVariableName variable) (SomeVariable variable)

data InstantiationFailure variable
    = ConcreteFailure (SomeVariable variable) (TermLike variable)
    | SymbolicFailure (SomeVariable variable) (TermLike variable)
    | UninstantiatedConcrete (SomeVariable variable)
    | UninstantiatedSymbolic (SomeVariable variable)

instance
    InternalVariable variable =>
    Pretty.Pretty (InstantiationFailure variable)
    where
    pretty (ConcreteFailure var term) =
        Pretty.vsep
            [ "Rule instantiation failure:"
            , Pretty.indent 4 (unparse var <> " is marked as concrete.")
            , Pretty.indent
                4
                ("However, " <> unparse term <> " is not concrete.")
            ]
    pretty (SymbolicFailure var term) =
        Pretty.vsep
            [ "Rule instantiation failure:"
            , Pretty.indent 4 (unparse var <> " is marked as symbolic.")
            , Pretty.indent
                4
                ("However, " <> unparse term <> " is not symbolic.")
            ]
    pretty (UninstantiatedConcrete var) =
        Pretty.vsep
            [ "Rule instantiation failure:"
            , Pretty.indent 4 (unparse var <> " is marked as concrete.")
            , Pretty.indent 4 "However, it was not instantiated."
            ]
    pretty (UninstantiatedSymbolic var) =
        Pretty.vsep
            [ "Rule instantiation failure:"
            , Pretty.indent 4 (unparse var <> " is marked as symbolic.")
            , Pretty.indent 4 "However, it was not instantiated."
            ]

-- | A rule which can be unified against a configuration
class UnifyingRule rule where
    type UnifyingRuleVariable rule

    -- | The pattern used for matching/unifying the rule with the configuration.
    matchingPattern :: rule -> TermLike (UnifyingRuleVariable rule)

    -- | The condition to be checked upon matching the rule
    precondition :: rule -> Predicate (UnifyingRuleVariable rule)

    -- | Refresh the variables of a rule.
    --    The free variables of a rule are implicitly quantified, so they are
    --    renamed to avoid collision with any variables in the given set.
    refreshRule ::
        InternalVariable (UnifyingRuleVariable rule) =>
        -- | Variables to avoid
        FreeVariables (UnifyingRuleVariable rule) ->
        rule ->
        (Renaming (UnifyingRuleVariable rule), rule)

    -- | Checks whether a given substitution is acceptable for a rule
    checkInstantiation ::
        InternalVariable (UnifyingRuleVariable rule) =>
        rule ->
        Map.Map
            (SomeVariable (UnifyingRuleVariable rule))
            (TermLike (UnifyingRuleVariable rule)) ->
        [InstantiationFailure (UnifyingRuleVariable rule)]
    checkInstantiation _ _ = []
    {-# INLINE checkInstantiation #-}
