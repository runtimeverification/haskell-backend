{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
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
import Kore.Internal.OrPattern (
    OrPattern,
 )
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
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Log.WarnUnsimplifiedPredicate (
    warnUnsimplifiedPredicate,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.Simplification.Ceil as Ceil
import Kore.Step.Simplification.Simplify
import Kore.Syntax (
    And (..),
    Bottom (..),
    Ceil (..),
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

{- | @NormalForm@ is the normal form result of simplifying 'Predicate'.
 The primary purpose of this form is to transmit to the external solver.
 Note that this is almost, but not quite, disjunctive normal form; see
 'simplifyNot' for the most notable exception.
-}
type NormalForm = MultiOr (MultiAnd (Predicate RewritingVariableName))

simplify ::
    forall simplifier.
    HasCallStack =>
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Predicate RewritingVariableName ->
    simplifier NormalForm
simplify sideCondition original =
    loop 0 (mkSingleton original)
  where
    limit :: Int
    limit = 4

    loop :: Int -> NormalForm -> simplifier NormalForm
    loop count input
        | count >= limit = do
            warnUnsimplifiedPredicate limit original input
            -- Return the current NormalForm. Do not iterate further.
            pure input
        | otherwise = do
            output <- MultiAnd.traverseOrAnd worker input
            if input == output
                then pure output
                else loop (count + 1) output

    replacePredicate = SideCondition.replacePredicate sideCondition

    simplifyTerm = simplifyTermLikeOnly sideCondition

    repr = SideCondition.toRepresentation sideCondition

    worker ::
        Predicate RewritingVariableName ->
        simplifier NormalForm
    worker predicate
        | Just predicate' <- replacePredicate predicate =
            worker predicate'
        | Predicate.isSimplified repr predicate =
            pure (mkSingleton predicate)
        | otherwise =
            case predicateF of
                AndF andF -> normalizeAnd =<< traverse worker andF
                OrF orF -> normalizeOr =<< traverse worker orF
                BottomF bottomF -> normalizeBottom =<< traverse worker bottomF
                TopF topF -> normalizeTop =<< traverse worker topF
                NotF notF -> simplifyNot =<< traverse worker notF
                ImpliesF impliesF -> simplifyImplies =<< traverse worker impliesF
                IffF iffF -> simplifyIff =<< traverse worker iffF
                CeilF ceilF ->
                    simplifyCeil sideCondition =<< traverse simplifyTerm ceilF
                _ -> simplifyPredicateTODO sideCondition predicate & MultiOr.observeAllT
      where
        _ :< predicateF = Recursive.project predicate

-- | Construct a 'NormalForm' from a single 'Predicate'.
mkSingleton ::
    Predicate RewritingVariableName ->
    NormalForm
mkSingleton = MultiOr.singleton . MultiAnd.singleton
{-# INLINE mkSingleton #-}

-- | See 'normalizeMultiAnd'.
normalizeAnd ::
    Applicative simplifier =>
    And sort NormalForm ->
    simplifier NormalForm
normalizeAnd = normalizeMultiAnd . foldMap MultiAnd.singleton

{- | @normalizeAnd@ obeys these laws:

 Distribution:

 @
 \\and(\\or(P[1], P[2]), P[3]) = \\or(\\and(P[1], P[3]), \\and(P[2], P[3]))
 @

 Identity:

 @
 \\and(\\top, P[1]) = P[1]
 @

 Annihilation:

 @
 \\and(\\bottom, _) = \\bottom
 @

 Idempotence:

 @
 \\and(P[1], P[1]) = P[1]
 @
-}
normalizeMultiAnd ::
    Applicative simplifier =>
    MultiAnd NormalForm ->
    simplifier NormalForm
normalizeMultiAnd andOr =
    pure . MultiOr.observeAll $ do
        -- andOr: \and(\or(_, _), \or(_, _))
        andAnd <- MultiAnd.traverse Logic.scatter andOr
        -- andAnd: \and(\and(_, _), \and(_, _))
        pure (fold andAnd)

{- | If the arguments of 'Or' are already in 'NormalForm', then normalization is
 trivial.

 @normalizeOr@ obeys these laws:

 Identity:

 @
 \\or(\\bottom, P[1]) = P[1]
 @

 Annihilation:

 @
 \\or(\\top, _) = \\top
 @

 Idempotence:

 @
 \\or(P[1], P[1]) = P[1]
 @
-}
normalizeOr ::
    Applicative simplifier =>
    Or sort NormalForm ->
    simplifier NormalForm
normalizeOr = pure . fold
{-# INLINE normalizeOr #-}

-- | 'Bottom' is regarded as trivially-normalizable.
normalizeBottom ::
    Applicative simplifier =>
    Bottom sort NormalForm ->
    simplifier NormalForm
normalizeBottom _ = pure MultiOr.bottom
{-# INLINE normalizeBottom #-}

-- | 'Top' is regarded as trivially-normalizable.
normalizeTop ::
    Applicative simplifier =>
    Top sort NormalForm ->
    simplifier NormalForm
normalizeTop _ = pure (MultiOr.singleton MultiAnd.top)
{-# INLINE normalizeTop #-}

{- | @simplifyNot@ obeys these laws:

 'Top':

 @
 \\not(\\top) = \\bottom
 @

 'Bottom':

 @
 \\not(\\bottom) = \\top
 @

 'Not':

 @
 \\not(\\not(P)) = P
 @

 'Or':

 @
 \\not(\\or(P[1], P[2])) = \\and(\\not(P[1]), \\not(P[2]))
 @

 @simplifyNot@ does not expand @\not(\and(_, _))@ into @\or(_, _)@, because
 the purpose of simplification is mostly to prepare 'Predicate' for the
 external solver or for the user, and the un-expanded form is more compact.
-}
simplifyNot ::
    forall simplifier sort.
    Monad simplifier =>
    Not sort NormalForm ->
    simplifier NormalForm
simplifyNot Not{notChild = multiOr, notSort} = do
    disjunctiveNormalForms <- Logic.observeAllT $ do
        multiAnd <- Logic.scatter multiOr
        normalizeNotAnd Not{notSort, notChild = multiAnd} & lift
    normalizeMultiAnd (MultiAnd.make disjunctiveNormalForms)

normalizeNotAnd ::
    forall simplifier sort.
    Monad simplifier =>
    Not sort (MultiAnd (Predicate RewritingVariableName)) ->
    simplifier NormalForm
normalizeNotAnd Not{notSort, notChild = predicates} =
    case toList predicates of
        [] ->
            -- \not(\top)
            bottom
        [predicate] ->
            case predicateF of
                NotF Not{notChild = result} ->
                    MultiAnd.fromPredicate result
                        & MultiOr.singleton
                        & pure
                _ -> fallback
          where
            _ :< predicateF = Recursive.project predicate
        _ -> fallback
  where
    fallback =
        -- \not(\and(_, ...))
        MultiAnd.toPredicate predicates
            & fromNot
            & Predicate.markSimplified
            & mkSingleton
            & pure
    bottom = normalizeBottom Bottom{bottomSort = notSort}

{- |
 @
 \\implies(L, R) = \\or(\\not(L), \\and(L, R))
 @

 Note: @L@ is carried through to the right-hand side of 'Implies' to maximize
 the information content of that branch.
-}
simplifyImplies ::
    Monad simplifier =>
    Implies sort NormalForm ->
    simplifier NormalForm
simplifyImplies Implies{impliesFirst, impliesSecond, impliesSort} = do
    negative <- mkNotSimplified impliesFirst
    positive <- mkAndSimplified impliesFirst impliesSecond
    mkOrSimplified negative positive
  where
    mkNotSimplified notChild =
        simplifyNot Not{notSort = impliesSort, notChild}
    mkAndSimplified andFirst andSecond =
        normalizeAnd And{andSort = impliesSort, andFirst, andSecond}
    mkOrSimplified orFirst orSecond =
        normalizeOr Or{orSort = impliesSort, orFirst, orSecond}

{- |
 @
 \\iff(P[1], P[2]) = \\or(\\and(\\not(P[1]), \\not(P[2])), \\and(P[1], P[2]))
 @
-}
simplifyIff ::
    Monad simplifier =>
    Iff sort NormalForm ->
    simplifier NormalForm
simplifyIff Iff{iffFirst, iffSecond, iffSort} = do
    orFirst <- do
        andFirst <- mkNotSimplified iffFirst
        andSecond <- mkNotSimplified iffSecond
        mkAndSimplified andFirst andSecond
    orSecond <- mkAndSimplified iffFirst iffSecond
    mkOrSimplified orFirst orSecond
  where
    mkNotSimplified notChild =
        simplifyNot Not{notSort = iffSort, notChild}
    mkAndSimplified andFirst andSecond =
        normalizeAnd And{andSort = iffSort, andFirst, andSecond}
    mkOrSimplified orFirst orSecond =
        normalizeOr Or{orSort = iffSort, orFirst, orSecond}

simplifyCeil ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Ceil sort (OrPattern RewritingVariableName) ->
    simplifier NormalForm
simplifyCeil sideCondition =
    Ceil.simplify sideCondition >=> return . MultiOr.map (from @(Condition _))
