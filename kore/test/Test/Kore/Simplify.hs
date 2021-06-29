module Test.Kore.Simplify (
    runSimplifier,
    runSimplifierSMT,
    runSimplifierBranch,
    simplifiedCondition,
    simplifiedOrCondition,
    simplifiedOrPattern,
    simplifiedPattern,
    simplifiedPredicate,
    simplifiedSubstitution,
    simplifiedTerm,

    -- * Re-exports
    Simplifier,
    SimplifierT,
    NoSMT,
    Env (..),
    Kore.MonadSimplify,
) where

import qualified Data.Functor.Foldable as Recursive
import qualified Kore.Attribute.Pattern.Simplified as Attribute
import qualified Kore.Attribute.PredicatePattern as Attribute.PPattern (
    setSimplified,
 )
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern (
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
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike (
    TermLike,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable (
    InternalVariable,
 )
import Kore.Rewrite.SMT.Declaration.All as SMT.AST (
    declare,
 )
import Kore.Simplify.Data (
    Env (..),
    Simplifier,
    SimplifierT,
 )
import qualified Kore.Simplify.Data as Kore
import Logic (
    LogicT,
 )
import Prelude.Kore
import SMT (
    NoSMT,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import qualified Test.SMT as Test

runSimplifierSMT :: Env Simplifier -> Simplifier a -> IO a
runSimplifierSMT env = Test.runSMT userInit . Kore.runSimplifier env
  where
    userInit = SMT.AST.declare Mock.smtDeclarations

runSimplifier :: Env (SimplifierT NoSMT) -> SimplifierT NoSMT a -> IO a
runSimplifier env = Test.runNoSMT . Kore.runSimplifier env

runSimplifierBranch ::
    Env (SimplifierT NoSMT) ->
    LogicT (SimplifierT NoSMT) a ->
    IO [a]
runSimplifierBranch env = Test.runNoSMT . Kore.runSimplifierBranch env

simplifiedTerm :: TermLike variable -> TermLike variable
simplifiedTerm =
    Recursive.unfold (simplifiedWorker . Recursive.project)
  where
    simplifiedWorker (attrs :< patt) =
        TermLike.setAttributeSimplified Attribute.fullySimplified attrs
            :< patt

simplifiedPredicate :: Predicate variable -> Predicate variable
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
