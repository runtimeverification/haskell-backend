{-# LANGUAGE TemplateHaskell #-}

module Kore.Step.Error
    ( StepError (..)
    , MissingAxiomVariables (..)
    , WhileApplyingAxiom (..)
    , missingAxiomVariables
    , whileApplyingAxiom
    , mapStepErrorVariables
    , stepErrorVariables
    , unificationToStepError
    , unificationOrSubstitutionToStepError
    -- * Re-exports
    , Typeable
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
import           Data.Type.Equality
import           Type.Reflection

import Control.Exception.Pretty
import Control.Exception.TH
import Kore.AST.Common
import Kore.Predicate.Predicate
import Kore.Step.AxiomPatterns
import Kore.Step.ExpandedPattern
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

{- | An exception to be thrown if axiom variables are not instantiated.

For the error message to be useful, the @variable@ type should be included in
the 'Pretty' instance of 'MissingAxiomVariables'. Update that instance when
adding a new variable type.

 -}
data MissingAxiomVariables =
        forall level variable.
        (Typeable level, Typeable variable) =>
        MissingAxiomVariables
            { variables :: !(Set (Variable level))
            , predicate :: !(Predicate level variable)
            , variableType :: !(TypeRep variable)
            }
    deriving (Typeable)

instance Pretty MissingAxiomVariables where
    pretty (MissingAxiomVariables { variables, predicate, variableType }) =
        vsep
            [ prettyVariables
            , "Expected \\bottom predicate, but instead found:"
            , prettyPredicate
            ]
      where
        message :: Doc ann
        message = "These axiom variables are missing from the substitution:"

        prettyVariables :: Doc ann
        prettyVariables = do
            (hang 4 . vsep)
                (message : map unparse (Set.toList variables))

        -- If the variable type cannot be resolved, at least show the type.
        fallback =
            vsep
                [   "The predicate cannot be displayed; \
                    \please report this as a bug."
                , "predicate :: " <> (pretty . show) (typeOf predicate)
                ]

        prettyPredicate =
            (fromMaybe fallback . asum)
                -- Try to get the set of missing variables in one of the known
                -- variable types. The Unparse instance for the variable type is
                -- resolved *here*, instead of where the exception is constructed.
                -- When a new variable type is added, it must be added to this list,
                -- but that should happen very rarely.
                [ prettyCommonPredicate
                ]

        prettyCommonPredicate :: Maybe (Doc ann)
        prettyCommonPredicate = do
            Refl <- testEquality variableType (typeRep :: TypeRep Variable)
            return (indent 4 $ unparse predicate)

instance Show MissingAxiomVariables where
    show = show . pretty

mkException 'PrettyException ''MissingAxiomVariables

{- | Construct a 'MissingAxiomVariables' exception.

For the error message to be useful, the @variable@ type should be included in
the 'Pretty' instance of 'MissingAxiomVariables'. Update that instance when
adding a new variable type.

 -}
missingAxiomVariables
    :: (Typeable level, Typeable variable)
    => Set (Variable level)
    -> Predicate level variable
    -> MissingAxiomVariables
missingAxiomVariables variables predicate =
    MissingAxiomVariables
        { variables
        , predicate
        , variableType = typeRep
        }

data WhileApplyingAxiom =
    forall level variable.
    Typeable level =>
    WhileApplyingAxiom
        { expandedPattern :: !(ExpandedPattern level variable)
        , axiomPattern :: !(AxiomPattern level)
        , exception :: !SomeException
        , variableType :: !(TypeRep variable)
        }
    deriving (Typeable)

instance Pretty WhileApplyingAxiom where
    pretty
        WhileApplyingAxiom
            { axiomPattern
            , expandedPattern
            , exception
            , variableType
            }
      =
        vsep
            [ "While applying axiom:"
            , indent 4 (prettyRewriteAxiomPattern axiomPattern)
            , "to the configuration:"
            , prettyExpandedPattern
            , fromMaybe
                (pretty $ displayException exception)
                (prettyException <$> fromException exception)
            ]
      where
        prettyException :: PrettyException -> Doc ann
        prettyException = pretty

        -- If the variable type cannot be resolved, at least show the type.
        fallback =
            vsep
                [   "The configuration cannot be displayed; \
                    \please report this as a bug."
                , indent 4 expandedPatternType
                ]
          where
            expandedPatternType =
                mappend
                    "expandedPattern :: "
                    $ pretty $ show
                    $ withTypeable variableType
                    $ typeOf expandedPattern

        prettyExpandedPattern =
            (fromMaybe fallback . asum)
                -- Try to get the set of missing variables in one of the known
                -- variable types. The Unparse instance for the variable type is
                -- resolved *here*, instead of where the exception is constructed.
                -- When a new variable type is added, it must be added to this list,
                -- but that should happen very rarely.
                [ prettyCommonExpandedPattern
                ]

        prettyCommonExpandedPattern :: Maybe (Doc ann)
        prettyCommonExpandedPattern = do
            Refl <- testEquality variableType (typeRep :: TypeRep Variable)
            return (indent 4 $ pretty expandedPattern)


instance Show WhileApplyingAxiom where
    show = show . pretty

mkException 'PrettyException ''WhileApplyingAxiom

whileApplyingAxiom
    ::  ( MonadCatch m, MonadThrow m
        , Typeable level, Typeable variable
        )
    => ExpandedPattern level variable
    -> AxiomPattern level
    -> m a
    -> m a
whileApplyingAxiom expandedPattern axiomPattern go =
    Monad.Catch.catchAll go handler
  where
    handler exception =
        Monad.Catch.throwM
            WhileApplyingAxiom
                { axiomPattern
                , expandedPattern
                , exception
                , variableType = typeRep
                }
