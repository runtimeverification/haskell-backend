{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.TermLike
    ( simplify
    , simplifyToOr
    , simplifyInternal
    ) where

import qualified Data.Functor.Foldable as Recursive

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import qualified Kore.Step.Simplification.And as And
                 ( simplify )
import qualified Kore.Step.Simplification.Application as Application
                 ( simplify )
import qualified Kore.Step.Simplification.Bottom as Bottom
                 ( simplify )
import qualified Kore.Step.Simplification.Builtin as Builtin
                 ( simplify )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( simplify )
import qualified Kore.Step.Simplification.CharLiteral as CharLiteral
                 ( simplify )
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.DomainValue as DomainValue
                 ( simplify )
import qualified Kore.Step.Simplification.Equals as Equals
                 ( simplify )
import qualified Kore.Step.Simplification.Exists as Exists
                 ( simplify )
import qualified Kore.Step.Simplification.Floor as Floor
                 ( simplify )
import qualified Kore.Step.Simplification.Forall as Forall
                 ( simplify )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( simplify )
import qualified Kore.Step.Simplification.Implies as Implies
                 ( simplify )
import qualified Kore.Step.Simplification.In as In
                 ( simplify )
import qualified Kore.Step.Simplification.Inhabitant as Inhabitant
                 ( simplify )
import qualified Kore.Step.Simplification.Mu as Mu
                 ( simplify )
import qualified Kore.Step.Simplification.Next as Next
                 ( simplify )
import qualified Kore.Step.Simplification.Not as Not
                 ( simplify )
import qualified Kore.Step.Simplification.Nu as Nu
                 ( simplify )
import qualified Kore.Step.Simplification.Or as Or
                 ( simplify )
import qualified Kore.Step.Simplification.Rewrites as Rewrites
                 ( simplify )
import qualified Kore.Step.Simplification.SetVariable as SetVariable
                 ( simplify )
import qualified Kore.Step.Simplification.StringLiteral as StringLiteral
                 ( simplify )
import qualified Kore.Step.Simplification.Top as Top
                 ( simplify )
import qualified Kore.Step.Simplification.Variable as Variable
                 ( simplify )
import           Kore.Unparser
import           Kore.Variables.Fresh

-- TODO(virgil): Add a Simplifiable class and make all pattern types
-- instances of that.

{-|'simplify' simplifies a `TermLike`, returning a 'Pattern'.
-}
simplify
    ::  ( SortedVariable variable
        , Show variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        )
    => PredicateSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Simplifier (Pattern variable)
simplify _substitutionSimplifier _axiomIdToEvaluator patt = do
    orPatt <- simplifyToOr patt
    return (OrPattern.toPattern orPatt)

{-|'simplifyToOr' simplifies a TermLike variable, returning an
'OrPattern'.
-}
simplifyToOr
    ::  ( SortedVariable variable
        , Show variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        )
    => TermLike variable
    -> Simplifier (OrPattern variable)
simplifyToOr =
    localSimplifierTermLike (const simplifier) . simplifyInternal
  where
    simplifier = termLikeSimplifier simplifyToOr

simplifyInternal
    ::  ( SortedVariable variable
        , Show variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        )
    => TermLike variable
    -> Simplifier (OrPattern variable)
simplifyInternal
    termLike@(Recursive.project -> attrs :< termLikeF)

  | EvaluatedF _ <- termLikeF =
    return (OrPattern.fromTermLike termLike)

  | MuF _ <- termLikeF =
    return (OrPattern.fromTermLike termLike)

  | NuF _ <- termLikeF =
    return (OrPattern.fromTermLike termLike)

  | otherwise = do
    substitutionSimplifier <- askSimplifierPredicate
    simplifier <- askSimplifierTermLike
    axiomIdToEvaluator <- askSimplifierAxioms
    traverse simplifyTerm termLikeF >>= \case
        AndF p         -> And.simplify p
        ApplicationF p -> Application.simplify (attrs :< p)
        BottomF p      -> return $ Bottom.simplify p
        BuiltinF p     -> return $ Builtin.simplify p
        CeilF p        -> Ceil.simplify p
        DomainValueF p -> return $ DomainValue.simplify p
        EqualsF p      -> Equals.simplify p
        ExistsF p ->
            Exists.simplify
                substitutionSimplifier simplifier axiomIdToEvaluator p
        FloorF p -> return $ Floor.simplify p
        ForallF p -> return $ Forall.simplify p
        IffF p ->
            Iff.simplify substitutionSimplifier simplifier axiomIdToEvaluator p
        ImpliesF p ->
            Implies.simplify
                substitutionSimplifier simplifier axiomIdToEvaluator p
        InF p ->
            In.simplify substitutionSimplifier simplifier axiomIdToEvaluator p
        InhabitantF s -> return $ Inhabitant.simplify s
        MuF p -> return $ Mu.simplify p
        -- TODO(virgil): Move next up through patterns.
        NextF p -> return $ Next.simplify p
        NotF p ->
            Not.simplify substitutionSimplifier simplifier axiomIdToEvaluator p
        NuF p -> return $ Nu.simplify p
        OrF p -> return $ Or.simplify p
        RewritesF p -> return $ Rewrites.simplify p
        StringLiteralF p -> return $ StringLiteral.simplify p
        CharLiteralF p -> return $ CharLiteral.simplify p
        TopF p -> return $ Top.simplify p
        VariableF p -> return $ Variable.simplify p
        SetVariableF p -> return $ SetVariable.simplify p
        EvaluatedF patterns ->
            -- This is technically impossible because this branch would not be
            -- chosen if termLikeF matched 'EvaluatedF', and 'traverse' (above)
            -- does not change the head of termLikeF. However, it is harmless to
            -- include this case here to convince the compiler that the case
            -- statement is complete.
            return (getEvaluated patterns)
