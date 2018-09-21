module Kore.Step.Error
    ( StepError (..)
    , mapStepErrorVariables
    , stepErrorVariables
    , unificationToStepError
    , unificationOrSubstitutionToStepError
    ) where

import Data.Bifunctor ( first )
import qualified Data.Set as Set

import Kore.Unification.Error

{-| 'StepError' represents the various error cases encountered while executing
a single step.
-}
data StepError level variable
    = StepErrorUnification UnificationError
    | StepErrorSubstitution (SubstitutionError level variable)
    deriving (Show, Eq)

{-| 'substitutionErrorVariables' extracts all variables in a
'SubstitutionError' as a set.
-}
stepErrorVariables
    :: Ord (variable level)
    => StepError level variable -> Set.Set (variable level)
stepErrorVariables (StepErrorUnification _)  = Set.empty
stepErrorVariables (StepErrorSubstitution a) = substitutionErrorVariables a

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
    :: Either (UnificationOrSubstitutionError level variable) a
    -> Either (StepError level variable) a
unificationOrSubstitutionToStepError (Left (UnificationError err)) =
    Left $ StepErrorUnification err
unificationOrSubstitutionToStepError (Left (SubstitutionError err)) =
    Left $ StepErrorSubstitution err
unificationOrSubstitutionToStepError (Right res) = Right res
