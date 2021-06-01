{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Step.Simplification.Predicate (
    simplify,
) where

import qualified Data.Functor.Foldable as Recursive
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.From
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
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
import Kore.Syntax (
    And (..),
    Bottom (..),
    Iff (..),
    Implies (..),
    Not (..),
    Or (..),
    Top (..),
 )
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
    loop . MultiOr.singleton . MultiAnd.singleton
  where
    loop :: DisjunctiveNormalForm -> simplifier DisjunctiveNormalForm
    loop input = do
        output <- MultiAnd.traverseOrAnd worker input
        (if input == output then pure else loop) output

    worker ::
        Predicate RewritingVariableName ->
        simplifier DisjunctiveNormalForm
    worker predicate =
        case predicateF of
            AndF andF -> normalizeAnd =<< traverse worker andF
            OrF orF -> normalizeOr =<< traverse worker orF
            BottomF bottomF -> normalizeBottom =<< traverse worker bottomF
            TopF topF -> normalizeTop =<< traverse worker topF
            NotF notF -> simplifyNot =<< traverse worker notF
            ImpliesF impliesF -> simplifyImplies =<< traverse worker impliesF
            IffF iffF -> simplifyIff =<< traverse worker iffF
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

normalizeBottom ::
    Applicative simplifier =>
    Bottom sort DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
normalizeBottom _ = pure MultiOr.bottom

normalizeTop ::
    Applicative simplifier =>
    Top sort DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
normalizeTop _ = pure (MultiOr.singleton MultiAnd.top)

simplifyNot ::
    Monad simplifier =>
    Not sort DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
simplifyNot notF@Not{notChild, notSort}
    | TopBottom.isTop notChild = normalizeBottom Bottom{bottomSort = notSort}
    | TopBottom.isBottom notChild = normalizeTop Top{topSort = notSort}
    | otherwise = normalizeNot notF

normalizeMultiAnd ::
    Applicative simplifier =>
    MultiAnd DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
normalizeMultiAnd andOr =
    pure . MultiOr.observeAll $ do
        -- andOr: \and(\or(_, _), \or(_, _))
        andAnd <- MultiAnd.traverse Logic.scatter andOr
        -- andAnd: \and(\and(_, _), \and(_, _))
        pure (fold andAnd)

normalizeNot ::
    forall simplifier sort.
    Monad simplifier =>
    Not sort DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
normalizeNot = normalizeNotOr
  where
    normalizeNotOr Not{notChild = multiOr, notSort} = do
        disjunctiveNormalForms <- Logic.observeAllT $ do
            multiAnd <- Logic.scatter multiOr
            normalizeNotAnd Not{notSort, notChild = multiAnd} & lift
        normalizeMultiAnd (MultiAnd.make disjunctiveNormalForms)
    normalizeNotAnd ::
        Not sort (MultiAnd (Predicate RewritingVariableName)) ->
        simplifier DisjunctiveNormalForm
    normalizeNotAnd Not{notChild = predicates} =
        normalized
            & MultiOr.singleton
            & pure
      where
        fallback =
            (fromNot $ MultiAnd.toPredicate predicates)
                & Predicate.markSimplified
                & MultiAnd.singleton
        normalized =
            case toList predicates of
                [predicate] ->
                    case predicateF of
                        NotF Not{notChild = result} ->
                            MultiAnd.fromPredicate result
                        _ -> fallback
                  where
                    _ :< predicateF = Recursive.project predicate
                _ -> fallback

simplifyImplies ::
    Monad simplifier =>
    Implies sort DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
simplifyImplies Implies{impliesFirst, impliesSecond, impliesSort}
    | TopBottom.isTop impliesFirst = pure impliesSecond
    | TopBottom.isBottom impliesFirst = normalizeTop Top{topSort = impliesSort}
    | otherwise = do
        impliesFirst' <-
            simplifyNot
                Not
                    { notSort = impliesSort
                    , notChild = impliesFirst
                    }
        impliesSecond' <-
            normalizeAnd
                And
                    { andSort = impliesSort
                    , andFirst = impliesFirst
                    , andSecond = impliesSecond
                    }
        pure (impliesFirst' <> impliesSecond')

simplifyIff ::
    Monad simplifier =>
    Iff sort DisjunctiveNormalForm ->
    simplifier DisjunctiveNormalForm
simplifyIff Iff{iffFirst, iffSecond, iffSort}
    | TopBottom.isTop iffFirst = pure iffSecond
    | TopBottom.isBottom iffFirst = mkNotSimplified iffSecond
    | TopBottom.isTop iffSecond = pure iffFirst
    | TopBottom.isBottom iffSecond = mkNotSimplified iffFirst
    | otherwise = do
        -- \iff(A, B) = \or( \and(\not(A), \not(B)), \and(A, B) )
        orFirst <- do
            andFirst <- mkNotSimplified iffFirst
            andSecond <- mkNotSimplified iffSecond
            mkAndSimplified andFirst andSecond
        orSecond <- mkAndSimplified iffFirst iffSecond
        normalizeOr Or{orSort = iffSort, orFirst, orSecond}
  where
    mkNotSimplified notChild =
        simplifyNot Not{notSort = iffSort, notChild}
    mkAndSimplified andFirst andSecond =
        normalizeAnd And{andSort = iffSort, andFirst, andSecond}
