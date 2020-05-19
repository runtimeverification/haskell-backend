{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

 -}

module Kore.Rewriting.UnifyingRule
    ( UnifyingRule (..)
    , InstantiationFailure (..)
    , Renaming
    ) where

import Prelude.Kore

import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.TermLike
    ( ElementVariable
    , InternalVariable
    , SetVariable
    , SortedVariable
    , TermLike
    )
import Kore.Unparser
import Kore.Variables.Fresh
    ( FreshPartialOrd
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )
import qualified Pretty

type Renaming variable =
    Map (UnifiedVariable variable) (UnifiedVariable variable)

data InstantiationFailure variable
    = ConcreteFailure (UnifiedVariable variable) (TermLike variable)
    | SymbolicFailure (UnifiedVariable variable) (TermLike variable)
    | UninstantiatedConcrete (UnifiedVariable variable)
    | UninstantiatedSymbolic (UnifiedVariable variable)

instance InternalVariable variable
    => Pretty.Pretty (InstantiationFailure variable)
  where
    pretty (ConcreteFailure var term) =
        Pretty.vsep
            [ "Rule instantiation failure:"
            , Pretty.indent 4 (unparse var <> " is marked as concrete.")
            , Pretty.indent 4
                ("However, " <> unparse term <> " is not concrete.")
            ]
    pretty (SymbolicFailure var term) =
        Pretty.vsep
            [ "Rule instantiation failure:"
            , Pretty.indent 4 (unparse var <> " is marked as symbolic.")
            , Pretty.indent 4
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
    -- | The pattern used for matching/unifying the rule with the configuration.
    matchingPattern :: rule variable -> TermLike variable

    -- | The condition to be checked upon matching the rule
    precondition :: rule variable -> Predicate variable

    {-| Refresh the variables of a rule.
    The free variables of a rule are implicitly quantified, so they are
    renamed to avoid collision with any variables in the given set.
     -}
    refreshRule
        :: InternalVariable variable
        => FreeVariables variable  -- ^ Variables to avoid
        -> rule variable
        -> (Renaming variable, rule variable)

    {-| Apply a given function to all variables in a rule. This is used for
    distinguishing rule variables from configuration variables.
    -}
    mapRuleVariables
        :: (Ord variable1, FreshPartialOrd variable2, SortedVariable variable2)
        => (ElementVariable variable1 -> ElementVariable variable2)
        -> (SetVariable variable1 -> SetVariable variable2)
        -> rule variable1
        -> rule variable2

    -- | Checks whether a given substitution is acceptable for a rule
    checkInstantiation
        :: InternalVariable variable
        => rule variable
        -> Map.Map (UnifiedVariable variable) (TermLike variable)
        -> [InstantiationFailure variable]
    checkInstantiation _ _ = []
    {-# INLINE checkInstantiation #-}
