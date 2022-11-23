module Test.Kore.Simplify (
    runSimplifierSMT,
    testRunSimplifier,
    testRunSimplifierBranch,
    simplifiedCondition,
    simplifiedOrCondition,
    simplifiedOrPattern,
    simplifiedPattern,
    simplifiedPredicate,
    simplifiedSubstitution,
    simplifiedTerm,

    -- * Re-exports
    Simplifier,
    SMT,
    Env (..),
    Kore.MonadSimplify,
) where

import Data.Functor.Foldable qualified as Recursive
import Kore.Attribute.Pattern.Simplified qualified as Attribute
import Kore.Attribute.PredicatePattern qualified as Attribute.PPattern (
    setSimplified,
 )
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import Kore.Internal.Conditional qualified as Conditional.DoNotUse
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern (
    splitTerm,
    withCondition,
 )
import Kore.Internal.Predicate (
    Predicate,
    PredicateF (..),
 )
import Kore.Internal.Substitution (
    Substitution,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike (
    TermLike,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Internal.Variable (
    InternalVariable,
 )
import Kore.Rewrite.SMT.Declaration (
    declareSortsSymbols,
 )
import Kore.Simplify.Simplify (
    Env (..),
    Simplifier,
 )
import Kore.Simplify.Simplify qualified as Kore
import Logic (
    LogicT,
 )
import Prelude.Kore
import SMT (
    SMT,
 )
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.SMT qualified as Test

runSimplifierSMT :: Env -> Simplifier a -> IO a
runSimplifierSMT env = Test.runSMT userInit . Kore.runSimplifier env
  where
    userInit = declareSortsSymbols Mock.smtDeclarations

testRunSimplifier :: Env -> Simplifier a -> IO a
testRunSimplifier env = Test.runNoSMT . Kore.runSimplifier env

testRunSimplifierBranch ::
    Env ->
    LogicT Simplifier a ->
    IO [a]
testRunSimplifierBranch env = Test.runNoSMT . Kore.runSimplifierBranch env

simplifiedTerm :: Hashable variable => TermLike variable -> TermLike variable
simplifiedTerm =
    Recursive.unfold (simplifiedWorker . Recursive.project)
  where
    simplifiedWorker (attrs :< patt) =
        TermLike.setAttributeSimplified Attribute.fullySimplified attrs
            :< patt

simplifiedPredicate :: Hashable variable => Predicate variable -> Predicate variable
simplifiedPredicate =
    Recursive.unfold (simplifiedWorker . Recursive.project)
  where
    simplifiedWorker (attrs :< patt) =
        Attribute.PPattern.setSimplified Attribute.fullySimplified attrs
            :< ( case patt of
                    CeilF ceil' -> CeilF (simplifiedTerm <$> ceil')
                    FloorF floor' -> FloorF (simplifiedTerm <$> floor')
                    EqualsF equals' -> EqualsF (simplifiedTerm <$> equals')
                    InF in' -> InF (simplifiedTerm <$> in')
                    _ -> patt
               )

simplifiedSubstitution ::
    InternalVariable variable =>
    Substitution variable ->
    Substitution variable
simplifiedSubstitution =
    Substitution.unsafeWrapFromAssignments
        . Substitution.unwrap
        . Substitution.mapTerms simplifiedTerm

simplifiedCondition ::
    InternalVariable variable =>
    Condition variable ->
    Condition variable
simplifiedCondition Conditional{term = (), predicate, substitution} =
    Conditional
        { term = ()
        , predicate = simplifiedPredicate predicate
        , substitution = simplifiedSubstitution substitution
        }

simplifiedPattern ::
    InternalVariable variable =>
    Pattern variable ->
    Pattern variable
simplifiedPattern patt =
    simplifiedTerm term `Pattern.withCondition` simplifiedCondition condition
  where
    (term, condition) = Pattern.splitTerm patt

simplifiedOrPattern ::
    InternalVariable variable =>
    OrPattern variable ->
    OrPattern variable
simplifiedOrPattern = OrPattern.map simplifiedPattern

simplifiedOrCondition ::
    InternalVariable variable =>
    OrCondition variable ->
    OrCondition variable
simplifiedOrCondition = OrPattern.map simplifiedCondition
