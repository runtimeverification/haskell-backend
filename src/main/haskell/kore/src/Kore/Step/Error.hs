module Kore.Step.Error
    ( StepError (..)
    , MissingAxiomVariables (..)
    , mapStepErrorVariables
    , stepErrorVariables
    , unificationToStepError
    , unificationOrSubstitutionToStepError
    , convertCommonExceptions
    ) where

import           Control.Monad.Catch
                 ( Exception (..), MonadCatch, MonadThrow, SomeException )
import qualified Control.Monad.Catch as Monad.Catch
import           Data.Bifunctor
                 ( first )
import           Data.Foldable
                 ( asum )
import           Data.Maybe
                 ( fromMaybe )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text.Prettyprint.Doc
import           Data.Typeable

import Control.Exception.Pretty
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.Unification.Error
import Kore.Unparser

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
    => StepError level variable -> Set (variable level)
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

data MissingAxiomVariables level variable =
    MissingAxiomVariables !(Set (variable level))
    deriving (Typeable)

instance Show (MissingAxiomVariables level variable) where
    show _ =
        "Uncaught exception: Variables from the left-hand side of the axiom \
        \are missing from the substitution!"

-- | @displayException@ is unhelpful, but this error is handled elsewhere.
instance
    (Typeable level, Typeable variable) =>
    Exception (MissingAxiomVariables level variable)

instance
    Unparse (variable level) =>
    Pretty (MissingAxiomVariables level variable)
  where
    pretty (MissingAxiomVariables missing) =
        (hang 4 . vsep) (message : map unparse (Set.toList missing))
      where
        message = "These axiom variables are missing from the substitution:"

convertCommonExceptions :: (MonadCatch m, MonadThrow m) => m a -> m a
convertCommonExceptions go =
    Monad.Catch.catchAll go rethrows
  where
    rethrows e =
        Monad.Catch.throwM $ fromMaybe e $ convertCases e

    convertCases :: SomeException -> Maybe SomeException
    convertCases e =
        asum
            [ fromException e >>= convertCommonMissingAxiomVariables
            ]

    convertCommonMissingAxiomVariables
        :: MissingAxiomVariables Object Variable
        -> Maybe SomeException
    convertCommonMissingAxiomVariables e =
        Just (toException (PrettyException (pretty e)))
