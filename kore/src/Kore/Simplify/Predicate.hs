{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Simplify.Predicate (
    simplify,
    extractFirstAssignment,
) where

import Kore.Rewrite.Function.Evaluator qualified as Axiom (
    evaluatePattern,
 )
import Kore.Unparser (unparseToString)
import Control.Error (
    MaybeT,
    maybeT,
    runMaybeT,
 )
import Data.Functor.Foldable qualified as Recursive
import Kore.Attribute.Synthetic (
    synthesize,
 )
import Kore.Internal.Condition qualified as Condition
import Data.Map.Strict qualified as Map
import Data.Monoid (
    First (..),
 )
import Kore.Attribute.Pattern.FreeVariables (
    freeVariableNames,
    occursIn,
 )
import Kore.Internal.From
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.MultiOr (
    MultiOr,
 )
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern (
    Condition,
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    Predicate,
    PredicateF (..),
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Substitution (
    pattern UnorderedAssignment,
 )
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike (
    TermLike,
    termLikeSort,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Log.WarnUnsimplified (
    warnUnsimplifiedPredicate,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Ceil qualified as Ceil
import Kore.Simplify.Equals qualified as Equals
import Kore.Simplify.In qualified as In
import Kore.Simplify.Not qualified as Not
import Kore.Simplify.Simplify
import Kore.Substitute
import Kore.Syntax (
    And (..),
    Bottom (..),
    Ceil (..),
    Equals (..),
    Exists (..),
    Floor (..),
    Forall (Forall),
    Iff (..),
    Implies (..),
    In (..),
    Not (..),
    Or (..),
    SomeVariableName,
    Sort,
    Top (..),
    variableName,
 )
import Kore.Syntax.Exists qualified as Exists
import Kore.Syntax.Forall qualified as Forall
import Logic
import Prelude.Kore

{- | @NormalForm@ is the normal form result of simplifying 'Predicate'.
 The primary purpose of this form is to transmit to the external solver.
 Note that this is almost, but not quite, disjunctive normal form; see
 'simplifyNot' for the most notable exception.
-}
type NormalForm = MultiOr (MultiAnd (Predicate RewritingVariableName))

toOrPattern :: Sort -> NormalForm -> OrPattern RewritingVariableName
toOrPattern sort =
    MultiOr.map
        ( Pattern.fromPredicateSorted sort
            . Predicate.makeMultipleAndPredicate
            . toList
        )

fromOrCondition :: OrCondition RewritingVariableName -> NormalForm
fromOrCondition = MultiOr.map (from @(Condition _))

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

    -- If the child 'TermLike' is a term representing a predicate,
    -- 'simplifyTerm' will not attempt to simplify it, so
    -- it should be transformed into a 'Predicate' and simplified
    -- accordingly.
    simplifyTerm' term
        | Right predicate <- Predicate.makePredicate term =
            toOrPattern (termLikeSort term) <$> worker predicate
        | otherwise =
            simplifyTerm sideCondition term

    repr = SideCondition.toRepresentation sideCondition

    -- Simplify the 'Predicate' bottom-up.
    -- The children of each node in the 'Predicate' tree are simplified
    -- either by calling the 'TermLike' simplifier (which only simplifies
    -- non-predicate terms) or, for 'Predicate's, by recursively calling
    -- this function.
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
                    simplifyCeil sideCondition =<< traverse simplifyTerm' ceilF
                FloorF floorF@(Floor _ _ child) ->
                    simplifyFloor (termLikeSort child) sideCondition
                        =<< traverse simplifyTerm' floorF
                ExistsF existsF ->
                    traverse worker (Exists.refreshExists avoid existsF)
                        >>= simplifyExists sideCondition
                ForallF forallF ->
                    traverse worker (Forall.refreshForall avoid forallF)
                        >>= simplifyForall sideCondition
                EqualsF equalsF@(Equals _ _ term _) ->
                    simplifyEquals sideCondition (termLikeSort term)
                        =<< traverse simplifyTerm' equalsF
                InF inF ->
                    simplifyIn sideCondition =<< traverse simplifyTerm' inF
      where
        _ :< predicateF = Recursive.project predicate
        ~avoid = freeVariableNames sideCondition

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
                    Predicate.toMultiAnd result
                        & MultiOr.singleton
                        & pure
                _ -> fallback
          where
            _ :< predicateF = Recursive.project predicate
        _ -> fallback
  where
    fallback =
        -- \not(\and(_, ...))
        Predicate.fromMultiAnd predicates
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
    Ceil.simplify sideCondition >=> return . fromOrCondition

{- |
 @
 \\floor(T) = \\not(\\ceil(\\not(T)))
 @
-}
simplifyFloor ::
    MonadSimplify simplifier =>
    Sort ->
    SideCondition RewritingVariableName ->
    Floor sort (OrPattern RewritingVariableName) ->
    simplifier NormalForm
simplifyFloor termSort sideCondition floor' = do
    notTerm <- mkNotSimplifiedTerm floorChild
    ceilNotTerm <- mkCeilSimplified notTerm
    mkNotSimplified ceilNotTerm
  where
    Floor{floorOperandSort, floorResultSort, floorChild} = floor'
    mkNotSimplified notChild =
        simplifyNot Not{notSort = floorResultSort, notChild}
    mkNotSimplifiedTerm notChild =
        Not.simplify sideCondition Not{notSort = termSort, notChild}
    mkCeilSimplified ceilChild =
        simplifyCeil
            sideCondition
            Ceil
                { ceilOperandSort = floorOperandSort
                , ceilResultSort = floorResultSort
                , ceilChild
                }

simplifyExists ::
    forall simplifier.
    Monad simplifier =>
    SideCondition RewritingVariableName ->
    Exists () RewritingVariableName NormalForm ->
    simplifier NormalForm
simplifyExists _ = \exists@Exists{existsChild} ->
    MultiOr.traverseOr (simplifyExistsAnd . ($>) exists) existsChild
  where
    simplifyExistsAnd ::
        (Exists () RewritingVariableName)
            (MultiAnd (Predicate RewritingVariableName)) ->
        simplifier NormalForm
    simplifyExistsAnd Exists{existsVariable, existsChild}
        | not (existsVariableName `occursIn` existsChild) =
            pure (MultiOr.singleton existsChild)
        | Just value <- extractFirstAssignment existsVariableName existsChild =
            applyAssignment existsVariableName value existsChild
                & MultiOr.singleton
                & pure
        | otherwise =
            fromExists existsVariable (Predicate.fromMultiAnd existsChild)
                & mkSingleton
                & pure
      where
        existsVariableName :: SomeVariableName RewritingVariableName
        existsVariableName = inject (variableName existsVariable)

    applyAssignment ::
        SomeVariableName RewritingVariableName ->
        TermLike RewritingVariableName ->
        MultiAnd (Predicate RewritingVariableName) ->
        MultiAnd (Predicate RewritingVariableName)
    applyAssignment someVariableName termLike predicates =
        let substitution = Map.singleton someVariableName termLike
            existsChild' = MultiAnd.map (substitute substitution) predicates
            valueCeil = MultiAnd.singleton (fromCeil_ termLike)
         in existsChild' <> valueCeil

{- |
 @
 \\forall(x, P) = \\not(\\exists(x, \\not(P)))
 @
-}
simplifyForall ::
    forall simplifier.
    Monad simplifier =>
    SideCondition RewritingVariableName ->
    Forall () RewritingVariableName NormalForm ->
    simplifier NormalForm
simplifyForall sideCondition forall' = do
    notChild <- mkNotSimplified forallChild
    existsNotChild <- mkExistsSimplified notChild
    mkNotSimplified existsNotChild
  where
    Forall{forallSort, forallVariable, forallChild} = forall'
    mkNotSimplified notChild =
        simplifyNot Not{notSort = forallSort, notChild}
    mkExistsSimplified existsChild =
        simplifyExists
            sideCondition
            Exists
                { existsSort = forallSort
                , existsVariable = forallVariable
                , existsChild
                }

extractFirstAssignment ::
    SomeVariableName RewritingVariableName ->
    MultiAnd (Predicate RewritingVariableName) ->
    Maybe (TermLike RewritingVariableName)
extractFirstAssignment someVariableName predicates =
    foldMap (First . extractAssignment) predicates
        & getFirst
  where
    extractAssignment ::
        Predicate RewritingVariableName ->
        Maybe (TermLike RewritingVariableName)
    extractAssignment predicate = do
        UnorderedAssignment _ termLike <-
            Substitution.retractAssignmentFor
                someVariableName
                predicate
        guard (TermLike.isFunctionPattern termLike)
        (guard . not) (someVariableName `occursIn` termLike)
        pure termLike

simplifyEquals ::
    forall simplifier sort.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Sort ->
    Equals sort (OrPattern RewritingVariableName) ->
    simplifier NormalForm
simplifyEquals sideCondition sort equals = do
    result <- runMaybeT applyUserSimplification
    maybe (Equals.simplify sideCondition equals') return result
        <&> MultiOr.map (from @(Condition _))
  where
    equals' =
        equals
            { equalsOperandSort = sort
            , equalsResultSort = sort
            }
    applyUserSimplification =
        let leftPatt = OrPattern.toPattern sort (equalsFirst equals')
            rightPatt = OrPattern.toPattern sort (equalsSecond equals')
         in applyEquations leftPatt rightPatt

    applyEquations ::
        Pattern RewritingVariableName ->
        Pattern RewritingVariableName ->
        MaybeT simplifier (OrCondition RewritingVariableName)
    applyEquations
        (Pattern.splitTerm -> (leftTerm, leftCondition))
        (Pattern.splitTerm -> (rightTerm, rightCondition))
      = do
        evaluatedTerms <-
            Axiom.evaluatePattern
                sideCondition
                Condition.top
                (TermLike.mkEquals sort leftTerm rightTerm)
                (const empty)
                -- & trace (unparseToString (TermLike.mkEquals sort leftTerm rightTerm))
        OrPattern.map
            ( Pattern.withoutTerm
            . flip Pattern.andCondition (leftCondition <> rightCondition)
            )
            evaluatedTerms
            & return

simplifyIn ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    In sort (OrPattern RewritingVariableName) ->
    simplifier NormalForm
simplifyIn sideCondition =
    In.simplify sideCondition >=> return . fromOrCondition
