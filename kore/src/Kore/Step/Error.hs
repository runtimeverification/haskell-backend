{-|
Module      : Kore.Step.Error
Description : Kore step evaluator errors
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.Error
    ( StepError (..)
    , mapStepErrorVariables
    , stepErrorVariables
    , unificationToStepError
    , unificationOrSubstitutionToStepError
    ) where

import           Data.Bifunctor
                 ( first )
import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
                 ( Pretty )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Unification.Error
import Kore.Unparser

{-| 'StepError' represents the various error cases encountered while executing
a single step.
-}
data StepError level variable
    = StepErrorUnification UnificationError
    -- ^ Error from a unification sub-step.
    | StepErrorSubstitution (SubstitutionError level variable)
    -- ^ Error from a substitution normalization sub-step.
    | StepErrorUnsupportedSymbolic
    -- ^ Error from an unsupported symbolic rule application.
    deriving (Show, Eq)

instance
    Unparse (variable level) =>
    Pretty (StepError level variable)
  where
    pretty (StepErrorUnification  err) = Pretty.pretty err
    pretty (StepErrorSubstitution err) = Pretty.pretty err
    pretty StepErrorUnsupportedSymbolic = "Unsupported symbolic rule"

{-| 'substitutionErrorVariables' extracts all variables in a
'SubstitutionError' as a set.
-}
stepErrorVariables
    :: Ord (variable level)
    => StepError level variable -> Set.Set (variable level)
stepErrorVariables (StepErrorUnification _)     = Set.empty
stepErrorVariables (StepErrorSubstitution a)    = substitutionErrorVariables a
stepErrorVariables StepErrorUnsupportedSymbolic = Set.empty

{-| 'mapStepErrorVariables' replaces all variables in a 'StepError' using
the provided mapping.
-}
mapStepErrorVariables
    :: (variableFrom level -> variableTo level)
    -> StepError level variableFrom
    -> StepError level variableTo
mapStepErrorVariables _ (StepErrorUnification a) = StepErrorUnification a
mapStepErrorVariables mapper (StepErrorSubstitution a) =
    StepErrorSubstitution (mapSubstitutionErrorVariables mapper a)
mapStepErrorVariables _ StepErrorUnsupportedSymbolic =
    StepErrorUnsupportedSymbolic

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
