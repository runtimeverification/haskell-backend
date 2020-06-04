{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation.Sentence
    ( fromSentenceAxiom
    , matchEquation, MatchEquationError (..)
    ) where

import Prelude.Kore

import qualified Data.Bifunctor as Bifunctor
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Axiom.Constructor
    ( Constructor (..)
    )
import Kore.Attribute.Functional
    ( Functional (..)
    )
import Kore.Attribute.Subsort
    ( Subsorts (..)
    )
import Kore.Equation.Equation
import Kore.Internal.Predicate
    ( NotPredicate
    , makePredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( InternalVariable
    , Symbol
    , TermLike
    , VariableName
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Syntax.Sentence
    ( SentenceAxiom (..)
    )
import qualified Kore.Verified as Verified

fromSentenceAxiom
    :: (Attribute.Axiom Symbol VariableName, Verified.SentenceAxiom)
    -> Either (MatchEquationError VariableName) (Equation VariableName)
fromSentenceAxiom (attributes, SentenceAxiom { sentenceAxiomPattern }) =
    matchEquation attributes sentenceAxiomPattern

data MatchEquationError variable
    = NotEquation !(TermLike variable)
    | RequiresError !(NotPredicate variable)
    | EnsuresError !(NotPredicate variable)
    | FunctionalAxiom
    | ConstructorAxiom
    | SubsortAxiom
    deriving (GHC.Generic)

instance SOP.Generic (MatchEquationError variable)

instance SOP.HasDatatypeInfo (MatchEquationError variable)

instance Debug variable => Debug (MatchEquationError variable)

{- | Match a term encoding an 'QualifiedAxiomPattern'.

@patternToAxiomPattern@ returns an error if the given 'TermLike' does
not encode a normal rewrite or function axiom.
-}
matchEquation
    :: forall variable
    .  InternalVariable variable
    => Attribute.Axiom Symbol variable
    -> TermLike variable
    -> Either (MatchEquationError variable) (Equation variable)
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
    match
        (TermLike.Implies_ _
            requires
            (TermLike.And_ _
                (TermLike.Equals_ _ _ left right)
                ensures
            )
        )
      = do
        requires' <- makePredicate requires & Bifunctor.first RequiresError
        ensures' <- makePredicate ensures & Bifunctor.first EnsuresError
        pure Equation
            { requires = requires'
            , left
            , right
            , ensures = ensures'
            , attributes
            }

    match (TermLike.Equals_ _ sort left right) =
        pure Equation
            { requires = Predicate.makeTruePredicate sort
            , left
            , right
            , ensures = Predicate.makeTruePredicate sort
            , attributes
            }

    match left@(TermLike.Ceil_ _ sort _) =
        pure Equation
            { requires = Predicate.makeTruePredicate sort
            , left
            , right = TermLike.mkTop sort
            , ensures = Predicate.makeTruePredicate sort
            , attributes
            }

    match termLike' = Left (NotEquation termLike')

    -- If the ensures and requires are the same, then the ensures is redundant.
    removeRedundantEnsures equation@Equation { requires, ensures }
      | ensures == requires =
        return equation { ensures = Predicate.makeTruePredicate sort }
      | otherwise = return equation
      where
        sort = termLikeSort (Predicate.unwrapPredicate ensures)
