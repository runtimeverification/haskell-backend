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
    , traverseStepErrorVariables
    , stepErrorVariables
    , unificationToStepError
    , unificationOrSubstitutionToStepError
    ) where

import           Data.Bifunctor
                 ( first )
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
-- TODO (thomas.tuegel): It would be nicer if 'StepError' was a Functor over
-- its variables.
mapStepErrorVariables
    :: (variableFrom level -> variableTo level)
    -> StepError level variableFrom
    -> StepError level variableTo
mapStepErrorVariables _ (StepErrorUnification a) = StepErrorUnification a
mapStepErrorVariables mapper (StepErrorSubstitution a) =
    StepErrorSubstitution (mapSubstitutionErrorVariables mapper a)

{- | Replace the variables in a 'StepError' using the given traversal.
 -}
-- TODO (thomas.tuegel): It would be nicer if 'StepError' was Traversable over
-- its variables.
traverseStepErrorVariables
    :: Applicative f
    => (variableFrom level -> f (variableTo level))
    -> StepError level variableFrom
    -> f (StepError level variableTo)
traverseStepErrorVariables traversal =
    \case
        StepErrorUnification err ->
            pure (StepErrorUnification err)
        StepErrorSubstitution err ->
            StepErrorSubstitution
                <$> traverseSubstitutionErrorVariables traversal err

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
