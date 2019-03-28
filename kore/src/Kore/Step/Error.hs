{-|
Module      : Kore.Step.Error
Description : Kore step evaluator errors
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.Error
    ( StepError (..)
    , UnsupportedSymbolic (..)
    , mapStepErrorVariables
    , unificationToStepError
    , unificationOrSubstitutionToStepError
    ) where

import Data.Bifunctor
       ( first )
import Data.Text.Prettyprint.Doc
       ( Pretty (..) )
import GHC.Generics
       ( Generic )

import           Kore.Step.Representation.PredicateSubstitution
                 ( PredicateSubstitution )
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.Rule
                 ( RulePattern )
import qualified Kore.Step.Rule as Rule
import           Kore.Unification.Error

data UnsupportedSymbolic level variable =
    UnsupportedSymbolic
        { unification :: !(PredicateSubstitution level variable)
        , rule        :: !(RulePattern level variable)
        }
    deriving (Eq, Generic, Show)

deriving instance
    (Ord level, Ord (variable level)) =>
    Ord (UnsupportedSymbolic level variable)

{-| 'StepError' represents the various error cases encountered while executing
a single step.
-}
data StepError level variable
    = StepErrorUnification UnificationError
    -- ^ Error from a unification sub-step.
    | StepErrorSubstitution (SubstitutionError level variable)
    -- ^ Error from a substitution normalization sub-step.
    | StepErrorUnsupportedSymbolic !(UnsupportedSymbolic level variable)
    -- ^ Error from an unsupported symbolic rule application.
    deriving (Show, Eq)

instance Pretty (StepError level variable) where
    pretty (StepErrorUnification _) = "Unification error:"
    pretty (StepErrorSubstitution _) = "Substitution error:"
    pretty (StepErrorUnsupportedSymbolic _) = "Unsupported symbolic result:"

{-| 'mapStepErrorVariables' replaces all variables in a 'StepError' using
the provided mapping.
-}
mapStepErrorVariables
    :: Ord (variableTo level)
    => (variableFrom level -> variableTo level)
    -> StepError level variableFrom
    -> StepError level variableTo
mapStepErrorVariables _ (StepErrorUnification a) = StepErrorUnification a
mapStepErrorVariables mapper (StepErrorSubstitution a) =
    StepErrorSubstitution (mapSubstitutionErrorVariables mapper a)
mapStepErrorVariables mapper (StepErrorUnsupportedSymbolic unsupported) =
    StepErrorUnsupportedSymbolic unsupported'
  where
    unsupported' =
        unsupported
            { unification =
                PredicateSubstitution.mapVariables mapper unification
            , rule = Rule.mapVariables mapper rule
            }
      where
        UnsupportedSymbolic { unification, rule } = unsupported

{-| 'unificationToStepError' converts an action with a 'UnificationError' into
an action with a 'StepError'.
-}
unificationToStepError
    :: Either UnificationError a
    -> Either (StepError level variable) a
unificationToStepError = first StepErrorUnification

{-| Converts a Unification or Substitution error to a step error
-}
unificationOrSubstitutionToStepError
    :: UnificationOrSubstitutionError level variable
    -> StepError level variable
unificationOrSubstitutionToStepError (UnificationError err) =
    StepErrorUnification err
unificationOrSubstitutionToStepError (SubstitutionError err) =
    StepErrorSubstitution err
