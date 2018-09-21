module Kore.Step.Error
    ( StepError (..)
    , mapStepErrorVariables
    , stepErrorVariables
    , unificationToStepError
    , unificationToStepErrorM
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
It takes a @bottom@ default value to convert unification errors into
'Bottom' if necessary.
-}
unificationToStepError
    :: a
    -> Either UnificationError a
    -> Either (StepError level variable) a
unificationToStepError _ (Left err)     = Left (StepErrorUnification err)
unificationToStepError _ (Right result) = Right result


unificationToStepErrorM
    :: Monad m
    => m (Either UnificationError a)
    -> m (Either (StepError level variable) a)
unificationToStepErrorM = fmap $ first StepErrorUnification

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
