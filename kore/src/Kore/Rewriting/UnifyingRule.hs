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
    ( InternalVariable
    , TermLike
    )
import Kore.Syntax.Variable
import Kore.Unparser
import Kore.Variables.Fresh
    ( FreshPartialOrd
    )
import qualified Pretty

type Renaming variable =
    Map (SomeVariableName variable) (SomeVariable1 variable)

data InstantiationFailure variable
    = ConcreteFailure (SomeVariable1 variable) (TermLike variable)
    | SymbolicFailure (SomeVariable1 variable) (TermLike variable)
    | UninstantiatedConcrete (SomeVariable1 variable)
    | UninstantiatedSymbolic (SomeVariable1 variable)

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
        :: Ord variable1
        => FreshPartialOrd variable2
        => AdjSomeVariableName (variable1 -> variable2)
        -> rule variable1
        -> rule variable2

    -- | Checks whether a given substitution is acceptable for a rule
    checkInstantiation
        :: InternalVariable variable
        => rule variable
        -> Map.Map (SomeVariable1 variable) (TermLike variable)
        -> [InstantiationFailure variable]
    checkInstantiation _ _ = []
    {-# INLINE checkInstantiation #-}
