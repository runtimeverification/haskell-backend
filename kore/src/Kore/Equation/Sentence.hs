{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Equation.Sentence (
    fromSentenceAxiom,
    matchEquation,
    MatchEquationError (..),
) where

import qualified Data.Bifunctor as Bifunctor
import Debug
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Axiom.Constructor (
    Constructor (..),
 )
import Kore.Attribute.Functional (
    Functional (..),
 )
import Kore.Attribute.Subsort (
    Subsorts (..),
 )
import Kore.Equation.Equation
import Kore.Internal.Predicate (
    NotPredicate,
    makePredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike (
    InternalVariable,
    NotTermLike,
    Symbol,
    TermLike,
    VariableName,
    makeTermLike,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Syntax.Sentence (
    SentenceAxiom (..),
 )
import Kore.Unparser (
    unparse,
 )
import qualified Kore.Validate as Validated
import Prelude.Kore
import Pretty

fromSentenceAxiom ::
    (Attribute.Axiom Symbol VariableName, Validated.SentenceAxiom) ->
    Either (MatchEquationError VariableName) (Equation VariableName)
fromSentenceAxiom (attributes, SentenceAxiom{sentenceAxiomPattern}) =
    matchEquation attributes sentenceAxiomPattern

data MatchEquationError variable
    = NotEquation (Validated.Pattern variable)
    | LeftError !(NotTermLike variable)
    | RightError !(NotTermLike variable)
    | RequiresError !(NotPredicate variable)
    | ArgumentError !(NotPredicate variable)
    | AntiLeftError !(NotPredicate variable)
    | EnsuresError !(NotPredicate variable)
    | FunctionalAxiom
    | ConstructorAxiom
    | SubsortAxiom
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

instance InternalVariable variable => Pretty (MatchEquationError variable) where
    pretty (NotEquation term) =
        Pretty.vsep
            [ "The given term is not an equation:"
            , unparse term
            ]
    pretty (RequiresError notPred) =
        Pretty.vsep
            [ "The equation's requires clause is not a predicate:"
            , pretty notPred
            , "This is a frontend bug. Please report this error at https://github.com/kframework/k/issues."
            ]
    pretty (ArgumentError notPred) =
        Pretty.vsep
            [ "The equation's argument clause is not a predicate:"
            , pretty notPred
            , "This is a frontend bug. Please report this error at https://github.com/kframework/k/issues."
            ]
    pretty (AntiLeftError notPred) =
        Pretty.vsep
            [ "The equation's anti-left clause is not a predicate:"
            , pretty notPred
            , "This is a frontend bug. Please report this error at https://github.com/kframework/k/issues."
            ]
    pretty (EnsuresError notPred) =
        Pretty.vsep
            [ "The equation's ensures clause is not a predicate:"
            , pretty notPred
            , "This is a frontend bug. Please report this error at https://github.com/kframework/k/issues."
            ]
    pretty FunctionalAxiom = "The term is a functional axiom."
    pretty ConstructorAxiom = "The term is a constructor axiom."
    pretty SubsortAxiom = "The term is a subsort axiom."

matchEquation ::
    InternalVariable variable =>
    Attribute.Axiom Symbol variable ->
    Validated.Pattern variable ->
    Either (MatchEquationError variable) (Equation variable)
matchEquation attributes validPattern
    | isFunctionalAxiom = Left FunctionalAxiom
    | isConstructorAxiom = Left ConstructorAxiom
    | isSubsortAxiom = Left SubsortAxiom
    | Validated.Forall_ _ _ child <- validPattern =
        matchEquation attributes child
    | otherwise =
        match validPattern >>= removeRedundantEnsures
  where
    isFunctionalAxiom = (isDeclaredFunctional . Attribute.functional) attributes
    isConstructorAxiom = (isConstructor . Attribute.constructor) attributes
    isSubsortAxiom = (not . null . getSubsorts . Attribute.subsorts) attributes

    -- function rule without priority
    -- TODO The pattern match below should be removed after the frontend is updated
    -- to use the correct format
    match
        ( Validated.Implies_
                _
                ( Validated.And_
                        _
                        requires
                        argument@( Validated.And_
                                        _
                                        (Validated.In_ _ _ _ _)
                                        _
                                    )
                    )
                ( Validated.And_
                        _
                        (Validated.Equals_ _ _ left right)
                        ensures
                    )
            ) =
            do
                left' <- makeTermLike left & Bifunctor.first LeftError
                right' <- makeTermLike right & Bifunctor.first RightError
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                argument' <- makePredicate argument & Bifunctor.first ArgumentError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Just argument'
                        , antiLeft = Nothing
                        , left = left'
                        , right = right'
                        , ensures = ensures'
                        , attributes
                        }
    match
        ( Validated.Implies_
                _
                ( Validated.And_
                        _
                        requires
                        argument@( Validated.And_
                                        _
                                        (Validated.In_ _ _ _ _)
                                        _
                                    )
                    )
                ( Validated.Equals_
                        _
                        _
                        left
                        (Validated.And_ _ right ensures)
                    )
            ) =
            do
                left' <- makeTermLike left & Bifunctor.first LeftError
                right' <- makeTermLike right & Bifunctor.first RightError
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                argument' <- makePredicate argument & Bifunctor.first ArgumentError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Just argument'
                        , antiLeft = Nothing
                        , left = left'
                        , right = right'
                        , ensures = ensures'
                        , attributes
                        }

    -- function rule with priority
    -- TODO The pattern match below should be removed after the frontend is updated
    -- to use the correct format
    match
        ( Validated.Implies_
                _
                ( Validated.And_
                        _
                        antiLeft
                        ( Validated.And_
                                _
                                requires
                                argument
                            )
                    )
                ( Validated.And_
                        _
                        (Validated.Equals_ _ _ left right)
                        ensures
                    )
            ) =
            do
                left' <- makeTermLike left & Bifunctor.first LeftError
                right' <- makeTermLike right & Bifunctor.first RightError
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                argument' <- makePredicate argument & Bifunctor.first ArgumentError
                antiLeft' <- makePredicate antiLeft & Bifunctor.first AntiLeftError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Just argument'
                        , antiLeft = Just antiLeft'
                        , left = left'
                        , right = right'
                        , ensures = ensures'
                        , attributes
                        }
    match
        ( Validated.Implies_
                _
                ( Validated.And_
                        _
                        antiLeft
                        ( Validated.And_
                                _
                                requires
                                argument
                            )
                    )
                ( Validated.Equals_
                        _
                        _
                        left
                        (Validated.And_ _ right ensures)
                    )
            ) =
            do
                left' <- makeTermLike left & Bifunctor.first LeftError
                right' <- makeTermLike right & Bifunctor.first RightError
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                argument' <- makePredicate argument & Bifunctor.first ArgumentError
                antiLeft' <- makePredicate antiLeft & Bifunctor.first AntiLeftError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Just argument'
                        , antiLeft = Just antiLeft'
                        , left = left'
                        , right = right'
                        , ensures = ensures'
                        , attributes
                        }
    -- TODO The pattern match below should be removed after the frontend is updated
    -- to use the correct format
    match
        ( Validated.Implies_
                _
                requires
                ( Validated.And_
                        _
                        (Validated.Equals_ _ _ left right)
                        ensures
                    )
            ) =
            do
                left' <- makeTermLike left & Bifunctor.first LeftError
                right' <- makeTermLike right & Bifunctor.first RightError
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Nothing
                        , antiLeft = Nothing
                        , left = left'
                        , right = right'
                        , ensures = ensures'
                        , attributes
                        }
    match
        ( Validated.Implies_
                _
                requires
                ( Validated.Equals_
                        _
                        _
                        left
                        (Validated.And_ _ right ensures)
                    )
            ) =
            do
                left' <- makeTermLike left & Bifunctor.first LeftError
                right' <- makeTermLike right & Bifunctor.first RightError
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Nothing
                        , antiLeft = Nothing
                        , left = left'
                        , right = right'
                        , ensures = ensures'
                        , attributes
                        }
    match (Validated.Equals_ _ _ left right) = do
        left' <- makeTermLike left & Bifunctor.first LeftError
        right' <- makeTermLike right & Bifunctor.first RightError
        pure
            Equation
                { requires = Predicate.makeTruePredicate
                , argument = Nothing
                , antiLeft = Nothing
                , left = left'
                , right = right'
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
    match left@(Validated.Ceil_ _ sort _) = do
        left' <- makeTermLike left & Bifunctor.first LeftError
        pure
            Equation
                { requires = Predicate.makeTruePredicate
                , argument = Nothing
                , antiLeft = Nothing
                , left = left'
                , right = TermLike.mkTop sort
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
    match validPattern = Left (NotEquation validPattern)

    -- If the ensures and requires are the same, then the ensures is redundant.
    removeRedundantEnsures equation@Equation{requires, ensures}
        | ensures == requires =
            return equation{ensures = Predicate.makeTruePredicate}
        | otherwise = return equation
