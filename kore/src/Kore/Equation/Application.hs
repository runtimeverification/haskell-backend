{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation.Application
    ( applyEquation
    , ApplyEquationResult
    , ApplyEquationError (..)
    , ApplyMatchError (..)
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
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
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
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.Axiom.Matcher
    ( MatchResult
    , matchIncremental
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.Step.SMT.Evaluator as SMT
import Kore.TopBottom
import Kore.Variables.Target
    ( Target
    )
import qualified Kore.Variables.Target as Target
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

type ApplyEquationResult variable =
    Either (ApplyEquationError variable) (Pattern variable)

data ApplyEquationError variable
    = NotMatched !(TermLike (Target variable)) !(Equation (Target variable))
    | ApplyMatchErrors
        !(MatchResult (Target variable))
        !(NonEmpty (ApplyMatchError (Target variable)))
    | RequiresNotMet !(Predicate variable) !(Predicate variable)
    deriving (Eq, Ord)
    deriving (GHC.Generic)

instance SOP.Generic (ApplyEquationError variable)

instance SOP.HasDatatypeInfo (ApplyEquationError variable)

instance Debug variable => Debug (ApplyEquationError variable)

instance (Debug variable, Diff variable) => Diff (ApplyEquationError variable)

{- | @ApplyMatchError@ represents a reason the match could not be applied.

 -}
data ApplyMatchError variable
    = NotConcrete (UnifiedVariable variable) (TermLike variable)
    -- ^ The variable was instantiated with a symbolic term where a concrete
    -- term was required.
    | NotSymbolic (UnifiedVariable variable) (TermLike variable)
    -- ^ The variable was instantiated with a concrete term where a symbolic
    -- term was required.
    | NotInstantiated (UnifiedVariable variable)
    -- ^ The variable was not instantiated.
    deriving (Eq, Ord)
    deriving (GHC.Generic)

instance SOP.Generic (ApplyMatchError variable)

instance SOP.HasDatatypeInfo (ApplyMatchError variable)

instance Debug variable => Debug (ApplyMatchError variable)

instance (Debug variable, Diff variable) => Diff (ApplyMatchError variable)

applyEquation
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition (Target variable)
    -> TermLike (Target variable)
    -> Equation variable
    -> simplifier (ApplyEquationResult variable)
applyEquation sideCondition termLike equation = runExceptT $ do
    let equationRenamed =
            targetEquationVariables sideCondition termLike equation
        notMatched = NotMatched termLike equationRenamed
        Equation { left } = equationRenamed
    matchResult <- match left termLike & noteT notMatched
    (equation', predicate) <- applyMatchResult equationRenamed matchResult
    let Equation { requires } = equation'
    checkRequires sideCondition predicate requires
    let Equation { right, ensures } = equation'
    return $ Pattern.withCondition right $ from @(Predicate _) ensures
  where
    match term1 term2 = MaybeT $ matchIncremental term1 term2

{- | Use a 'MatchResult' to instantiate an 'Equation'.

The 'MatchResult' must cover all the free variables of the 'Equation'; this
condition is not checked, but enforced by the matcher. The result is the
'Equation' and any 'Predicate' assembled during matching, both instantiated by
the 'MatchResult'.

Throws 'ApplyMatchErrors' if there is a problem with the 'MatchResult'.

 -}
applyMatchResult
    :: forall monad variable
    .   Monad monad
    =>  InternalVariable variable
    =>  Equation (Target variable)
    ->  MatchResult (Target variable)
    ->  ExceptT (ApplyEquationError variable) monad
            (Equation variable, Predicate variable)
applyMatchResult equation matchResult@(predicate, substitution) =
    case errors of
        x : xs -> throwE $ ApplyMatchErrors matchResult (x :| xs)
        _      -> return (equation', predicate')
  where
    errors = notConcretes <> notSymbolics

    predicate' =
        Predicate.substitute substitution predicate
        & Predicate.mapVariables Target.unTargetElement Target.unTargetSet
    equation' =
        Equation.substitute substitution equation
        & Equation.mapVariables Target.unTargetElement Target.unTargetSet

    Equation { attributes } = equation
    concretes =
        attributes
        & Attribute.concrete & Attribute.unConcrete
        & FreeVariables.getFreeVariables
    symbolics =
        attributes
        & Attribute.symbolic & Attribute.unSymbolic
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

{- | Check that the requires from matching and the 'Equation' hold.

Throws 'RequiresNotMet' if the 'Predicate's do not hold under the
'SideCondition'.

 -}
checkRequires
    :: forall simplifier variable
    .  MonadSimplify simplifier
    => InternalVariable variable
    => SideCondition (Target variable)
    -> Predicate variable  -- ^ requires from matching
    -> Predicate variable  -- ^ requires from 'Equation'
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
            >>= SMT.filterBranch . withSideCondition
            >>= return . snd
    -- Collect the simplified results. If they are \bottom, then \and(predicate,
    -- requires) is valid; otherwise, the required pre-conditions are not met
    -- and the rule will not be applied.
    & (OrCondition.gather >=> assertBottom)
  where
    simplifyCondition = Simplifier.simplifyCondition sideCondition'

    -- TODO (thomas.tuegel): Do not unwrap sideCondition.
    sideCondition' =
        SideCondition.mapVariables
            Target.unTargetElement
            Target.unTargetSet
            sideCondition

    assertBottom orCondition
      | isBottom orCondition = done
      | otherwise            = requiresNotMet
    done = return ()
    requiresNotMet = throwE (RequiresNotMet predicate requires)

    -- Pair a configuration with sideCondition for evaluation by the solver.
    withSideCondition = (,) sideCondition'

    withoutAxioms =
        fmap Condition.forgetSimplified
        . Simplifier.localSimplifierAxioms (const mempty)
    withAxioms = id

{- | Make the 'Equation' variables distinct from the initial pattern.

The variables are marked 'Target' and renamed to avoid any variables in the
'SideCondition' or the 'TermLike'.

 -}
targetEquationVariables
    :: forall variable
    .  InternalVariable variable
    => SideCondition (Target variable)
    -> TermLike (Target variable)
    -> Equation variable
    -> Equation (Target variable)
targetEquationVariables sideCondition initial =
    snd
    . Equation.refreshVariables avoiding
    . Equation.mapVariables Target.mkElementTarget Target.mkSetTarget
  where
    avoiding = freeVariables sideCondition <> freeVariables initial
