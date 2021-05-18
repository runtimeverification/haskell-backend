{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Step.Simplification.Predicate (
    simplify,
) where

import qualified Data.Functor.Foldable as Recursive
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd (MultiAnd)
import Kore.Internal.MultiOr (
    MultiOr,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Condition,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
    PredicateF (..),
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.Simplify
import Kore.Syntax (And, Or)
import qualified Kore.TopBottom as TopBottom
import Kore.Unparser
import Logic
import Prelude.Kore
import qualified Pretty

{- | Simplify the 'Predicate' once.

@simplifyPredicate@ does not attempt to apply the resulting substitution and
re-simplify the result.

See also: 'simplify'
-}
simplifyPredicateTODO ::
    ( HasCallStack
    , MonadSimplify simplifier
    ) =>
    SideCondition RewritingVariableName ->
    Predicate RewritingVariableName ->
    LogicT simplifier (MultiAnd (Predicate RewritingVariableName))
simplifyPredicateTODO sideCondition predicate = do
    patternOr <-
        simplifyTermLike sideCondition (Predicate.fromPredicate_ predicate)
            & lift
    -- Despite using lift above, we do not need to
    -- explicitly check for \bottom because patternOr is an OrPattern.
    from @(Condition _) @(MultiAnd (Predicate _)) <$> scatter (OrPattern.map eraseTerm patternOr)
  where
    eraseTerm conditional
        | TopBottom.isTop (Pattern.term conditional) =
            Conditional.withoutTerm conditional
        | otherwise =
            (error . show . Pretty.vsep)
                [ "Expecting a \\top term, but found:"
                , unparse conditional
                ]

type DisjunctiveNormalForm =
    MultiOr (MultiAnd (Predicate RewritingVariableName))

simplify ::
    forall simplifier.
    ( HasCallStack
    , MonadSimplify simplifier
    ) =>
    SideCondition RewritingVariableName ->
    Predicate RewritingVariableName ->
    simplifier DisjunctiveNormalForm
simplify sideCondition =
    worker
  where
    worker ::
        Predicate RewritingVariableName ->
        simplifier DisjunctiveNormalForm
    worker predicate =
        case predicateF of
            AndF andF -> do
                let andF' = worker <$> andF
                normalizeAnd =<< sequence andF'
            OrF orF -> do
                let orF' = worker <$> orF
                normalizeOr =<< sequence orF'
            _ -> simplifyPredicateTODO sideCondition predicate & MultiOr.observeAllT
      where
        _ :< predicateF = Recursive.project predicate

normalizeAnd ::
    Applicative simplifier =>
    And sort DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
normalizeAnd andOr =
    pure . MultiOr.observeAll $ do
        -- andOr: \and(\or(_, _), \or(_, _))
        andAnd <- traverse Logic.scatter andOr
        -- andAnd: \and(\and(_, _), \and(_, _))
        let multiAnd = fold andAnd
        pure multiAnd

normalizeOr ::
    Applicative simplifier =>
    Or sort DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
normalizeOr = pure . fold
