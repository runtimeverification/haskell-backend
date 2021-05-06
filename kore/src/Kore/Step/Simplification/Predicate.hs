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

simplify ::
    ( HasCallStack
    , MonadSimplify simplifier
    ) =>
    SideCondition RewritingVariableName ->
    Predicate RewritingVariableName ->
    LogicT simplifier (MultiAnd (Predicate RewritingVariableName))
simplify sideCondition =
    worker
  where
    worker predicate =
        case predicateF of
            AndF andF -> do
                let andF' = worker <$> andF
                distributeAnd andF'
            OrF orF -> do
                let orF' = worker <$> orF
                distributeOr orF'
            _ -> simplifyPredicateTODO sideCondition predicate
      where
        _ :< predicateF = Recursive.project predicate

distributeAnd ::
    And sort (LogicT simplifier (MultiAnd (Predicate RewritingVariableName))) ->
    LogicT simplifier (MultiAnd (Predicate RewritingVariableName))
distributeAnd andF = fold <$> sequence andF

distributeOr ::
    Or sort (LogicT simplifier conjunction) ->
    LogicT simplifier conjunction
distributeOr = foldr1 (<|>)
