{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation.Application
    ( applyEquation
    , ApplyEquationResult
    , ApplyEquationError (..)
    , InstantiationError (..)
    ) where

import Prelude.Kore

import Control.Error
    ( ExceptT
    , MaybeT (..)
    , noteT
    , runExceptT
    , throwE
    )
import Control.Monad
    ( (>=>)
    )
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Equation.Equation
    ( Equation (..)
    )
import qualified Kore.Equation.Equation as Equation
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeAndPredicate
    , makeNotPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Axiom.Matcher
    ( MatchResult
    , matchIncremental
    )
import qualified Kore.Step.Simplification.Data as Simplifier
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import qualified Kore.Step.SMT.Evaluator as SMT
import Kore.TopBottom
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

type ApplyEquationResult variable =
    Either (ApplyEquationError variable) (Pattern variable)

data ApplyEquationError variable
    = NotMatched !(TermLike variable) !(Equation variable)
    | InstantiationErrors
        !(MatchResult variable)
        !(NonEmpty (InstantiationError variable))
    | RequiresNotMet !(Predicate variable) !(Predicate variable)

{- | @InstantiationError@ represents a reason to reject the instantiation of
an 'Equation'.
 -}
data InstantiationError variable
    = NotConcrete (UnifiedVariable variable) (TermLike variable)
    -- ^ The variable was instantiated with a symbolic term where a concrete
    -- term was required.
    | NotSymbolic (UnifiedVariable variable) (TermLike variable)
    -- ^ The variable was instantiated with a concrete term where a symbolic
    -- term was required.
    | NotInstantiated (UnifiedVariable variable)
    -- ^ The variable was not instantiated.

applyEquation
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition variable
    -> TermLike variable
    -> Equation variable
    -> simplifier (ApplyEquationResult variable)
applyEquation sideCondition termLike equation = runExceptT $ do
    let Equation { left } = equation
    matchResult <- match left termLike & noteT notMatched
    (equation', predicate) <- applyMatchResult equation matchResult
    let Equation { requires } = equation'
    checkRequires sideCondition predicate requires
    let Equation { right, ensures } = equation'
    return $ Pattern.withCondition right $ from @(Predicate _) ensures
  where
    match term1 term2 = MaybeT $ matchIncremental term1 term2
    notMatched = NotMatched termLike equation

applyMatchResult
    :: forall monad variable
    .   Monad monad
    =>  InternalVariable variable
    =>  Equation variable
    ->  MatchResult variable
    ->  ExceptT (ApplyEquationError variable) monad
            (Equation variable, Predicate variable)
applyMatchResult equation matchResult@(predicate, substitution) =
    case errors of
        x : xs -> throwE $ InstantiationErrors matchResult (x :| xs)
        _      -> return (equation', predicate')
  where
    errors = notConcretes <> notSymbolics

    predicate' = Predicate.substitute substitution predicate
    equation' = Equation.substitute substitution equation

    Equation { attributes } = equation
    concretes =
        attributes
        & Attribute.unConcrete . Attribute.concrete
        & FreeVariables.getFreeVariables
    symbolics =
        attributes
        & Attribute.unSymbolic . Attribute.symbolic
        & FreeVariables.getFreeVariables
    checkConcrete var =
        case Map.lookup var substitution of
            Nothing -> Just (NotInstantiated var)
            Just termLike
              | TermLike.isConstructorLike termLike -> Nothing
              | otherwise -> Just (NotConcrete var termLike)
    checkSymbolic var =
        case Map.lookup var substitution of
            Nothing -> Just (NotInstantiated var)
            Just termLike
              | TermLike.isConstructorLike termLike ->
                Just (NotSymbolic var termLike)
              | otherwise -> Nothing
    notConcretes = mapMaybe checkConcrete (Set.toList concretes)
    notSymbolics = mapMaybe checkSymbolic (Set.toList symbolics)

checkRequires
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition variable
    -> Predicate variable
    -> Predicate variable
    -> ExceptT (ApplyEquationError variable) simplifier ()
checkRequires sideCondition predicate requires =
    do
        let requires' = makeAndPredicate predicate requires
            -- The condition to refute:
            condition :: Condition variable
            condition = from @(Predicate _) (makeNotPredicate requires')
        return condition
            -- First try to refute 'condition' without user-defined axioms:
            >>= withoutAxioms . simplifyCondition
            -- Next try to refute 'condition' including user-defined axioms:
            >>= withAxioms . simplifyCondition
            -- Finally, try to refute the simplified 'condition' using the
            -- external solver:
            >>= SMT.filterBranch
    -- Collect the simplified results. If they are \bottom, then \and(predicate,
    -- requires) is valid; otherwise, the required pre-conditions are not met
    -- and the rule will not be applied.
    & (OrCondition.gather >=> assertBottom)
  where
    simplifyCondition = Simplifier.simplifyCondition sideCondition

    assertBottom orCondition
      | isBottom orCondition = done
      | otherwise            = requiresNotMet
    done = return ()
    requiresNotMet = throwE (RequiresNotMet predicate requires)

    withoutAxioms =
        fmap Condition.forgetSimplified
        . Simplifier.localSimplifierAxioms (const mempty)
    withAxioms = id
