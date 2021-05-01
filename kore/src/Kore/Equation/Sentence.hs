{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
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
    Symbol,
    TermLike,
    VariableName,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Syntax.Sentence (
    SentenceAxiom (..),
 )
import qualified Kore.Verified as Verified
import Prelude.Kore

fromSentenceAxiom ::
    (Attribute.Axiom Symbol VariableName, Verified.SentenceAxiom) ->
    Either (MatchEquationError VariableName) (Equation VariableName)
fromSentenceAxiom (attributes, SentenceAxiom{sentenceAxiomPattern}) =
    matchEquation attributes sentenceAxiomPattern

data MatchEquationError variable
    = NotEquation !(TermLike variable)
    | RequiresError !(NotPredicate variable)
    | ArgumentError !(NotPredicate variable)
    | AntiLeftError !(NotPredicate variable)
    | EnsuresError !(NotPredicate variable)
    | FunctionalAxiom
    | ConstructorAxiom
    | SubsortAxiom
    deriving (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

matchEquation ::
    forall variable.
    InternalVariable variable =>
    Attribute.Axiom Symbol variable ->
    TermLike variable ->
    Either (MatchEquationError variable) (Equation variable)
matchEquation attributes termLike
    | isFunctionalAxiom = Left FunctionalAxiom
    | isConstructorAxiom = Left ConstructorAxiom
    | isSubsortAxiom = Left SubsortAxiom
    | TermLike.Forall_ _ _ child <- termLike = matchEquation attributes child
    | otherwise = match termLike >>= removeRedundantEnsures
  where
    isFunctionalAxiom = (isDeclaredFunctional . Attribute.functional) attributes
    isConstructorAxiom = (isConstructor . Attribute.constructor) attributes
    isSubsortAxiom = (not . null . getSubsorts . Attribute.subsorts) attributes

    -- function rule without priority
    match
        ( TermLike.Implies_
                _
                ( TermLike.And_
                        _
                        requires
                        argument@( TermLike.And_
                                        _
                                        (TermLike.In_ _ _ _ _)
                                        _
                                    )
                    )
                ( TermLike.And_
                        _
                        (TermLike.Equals_ _ _ left right)
                        ensures
                    )
            ) =
            do
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                argument' <- makePredicate argument & Bifunctor.first ArgumentError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Just argument'
                        , antiLeft = Nothing
                        , left
                        , right
                        , ensures = ensures'
                        , attributes
                        }

    -- function rule with priority
    match
        ( TermLike.Implies_
                _
                ( TermLike.And_
                        _
                        antiLeft
                        ( TermLike.And_
                                _
                                requires
                                argument
                            )
                    )
                ( TermLike.And_
                        _
                        (TermLike.Equals_ _ _ left right)
                        ensures
                    )
            ) =
            do
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                argument' <- makePredicate argument & Bifunctor.first ArgumentError
                antiLeft' <- makePredicate antiLeft & Bifunctor.first AntiLeftError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Just argument'
                        , antiLeft = Just antiLeft'
                        , left
                        , right
                        , ensures = ensures'
                        , attributes
                        }
    match
        ( TermLike.Implies_
                _
                requires
                ( TermLike.And_
                        _
                        (TermLike.Equals_ _ _ left right)
                        ensures
                    )
            ) =
            do
                requires' <- makePredicate requires & Bifunctor.first RequiresError
                ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
                pure
                    Equation
                        { requires = requires'
                        , argument = Nothing
                        , antiLeft = Nothing
                        , left
                        , right
                        , ensures = ensures'
                        , attributes
                        }
    match (TermLike.Equals_ _ _ left right) =
        pure
            Equation
                { requires = Predicate.makeTruePredicate
                , argument = Nothing
                , antiLeft = Nothing
                , left
                , right
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
    match left@(TermLike.Ceil_ _ sort _) =
        pure
            Equation
                { requires = Predicate.makeTruePredicate
                , argument = Nothing
                , antiLeft = Nothing
                , left
                , right = TermLike.mkTop sort
                , ensures = Predicate.makeTruePredicate
                , attributes
                }
    match termLike' = Left (NotEquation termLike')

    -- If the ensures and requires are the same, then the ensures is redundant.
    removeRedundantEnsures equation@Equation{requires, ensures}
        | ensures == requires =
            return equation{ensures = Predicate.makeTruePredicate}
        | otherwise = return equation
