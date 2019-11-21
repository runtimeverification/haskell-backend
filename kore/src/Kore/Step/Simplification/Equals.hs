{-|
Module      : Kore.Step.Simplification.Equals
Description : Tools for Equals pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Equals
    ( makeEvaluate
    , makeEvaluateTerms
    , simplify
    , termEquals
    ) where

import Control.Error
    ( MaybeT (..)
    )
import qualified Control.Monad as Monad
    ( when
    )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Functor.Foldable as Recursive
import Data.Maybe
    ( fromMaybe
    )
import qualified GHC.Stack as GHC

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( make
    )
import qualified Kore.Internal.MultiOr as MultiOr
    ( make
    )
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( pattern PredicateTrue
    , makeEqualsPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( pattern Equals_
    , TermLike
    , pattern Top_
    , isFunctionPattern
    , mkTop_
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Sort
    ( Sort
    )
import Kore.Step.Simplification.AndTerms
    ( maybeTermEquals
    )
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    , SimplifiableF (..)
    )
import qualified Kore.Step.Simplification.Simplifiable as Unsimplified
    ( mkAnd
    , mkCeil
    , mkIff
    , mkImplies
    , mkNot
    , mkOr
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromMultiAnd
    , fromMultiOr
    , fromOrCondition
    , fromOrPattern
    , fromPattern
    , fromPredicate
    , fromTermLike
    , top
    )
import Kore.Step.Simplification.Simplify
import Kore.Step.Simplification.SubstitutionSimplifier
    ( SubstitutionSimplifier (SubstitutionSimplifier)
    )
import qualified Kore.Step.Simplification.SubstitutionSimplifier as SubstitutionSimplifier
    ( SubstitutionSimplifier (..)
    , substitutionSimplifier
    )
import Kore.Syntax.Equals
    ( Equals (Equals)
    )
import qualified Kore.Syntax.Equals as Equals.DoNotUse
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.UnifierT as UnifierT
    ( scatter
    )
import Kore.Unification.UnifierT
    ( UnifierT
    , runUnifierT
    )
import Kore.Unification.Unify
    ( MonadUnify
    )

{-|'simplify' simplifies an 'Equals' pattern made of 'OrPattern's.

This uses the following simplifications
(t = term, s = substitution, p = predicate):

* Equals(a, a) = true
* Equals(phi, psi1 or psi2 or ... or psin), when phi is functional
    = or
        ( not ceil (phi) and not ceil(psi1) and ... and not ceil (psin)
        , and
            ( ceil(phi)
            , ceil(psi1) or ceil(psi2) or  ... or ceil(psin)
            , ceil(psi1) implies phi == psi1)
            , ceil(psi2) implies phi == psi2)
            ...
            , ceil(psin) implies phi == psin)
            )
        )
* Equals(t1 and t2) = ceil(t1 and t2) or (not ceil(t1) and not ceil(t2))
    if t1 and t2 are functions.
* Equals(t1 and p1 and s1, t2 and p2 and s2) =
    Or(
        And(
            Equals(t1, t2)
            And(ceil(t1) and p1 and s1, ceil(t2) and p2 and s2))
        And(not(ceil(t1) and p1 and s1), not(ceil(t2) and p2 and s2))
    )
    + If t1 and t2 can't be bottom, then this becomes
      Equals(t1 and p1 and s1, t2 and p2 and s2) =
        Or(
            And(
                Equals(t1, t2)
                And(p1 and s1, p2 and s2))
            And(not(p1 and s1), not(p2 and s2))
        )
    + If the two terms are constructors, then this becomes
      Equals(
        constr1(t1, t2, ...) and p1 and s1,
        constr2(t1', t2', ...) and p2 and s2)
        = Or(
            and(
                (p1 and s2) iff (p2 and s2),
                constr1 == constr2,
                ceil(constr1(t1, t2, ...), constr2(t1', t2', ...))
                Equals(t1, t1'), Equals(t2, t2'), ...
                )
            and(
                not(ceil(constr1(t1, t2, ...)) and p1 and s1),
                not(ceil(constr2(t1', t2', ...)), p2 and s2)
                )
        )
      Note that when expanding Equals(t1, t1') recursively we don't need to
      put the ceil conditions again, since we already asserted that.
      Also note that ceil(constr(...)) is simplifiable.
    + If the first term is a variable and the second is functional,
      then we get a substitution:
        Or(
            And(
                [t1 = t2]
                And(p1 and s1, p2 and s2))
            And(not(p1 and s1), not(p2 and s2))
        )
    + If the terms are Top, this becomes
      Equals(p1 and s1, p2 and s2) = Iff(p1 and s1, p2 and s2)
    + If the predicate and substitution are Top, then the result is any of
      Equals(t1, t2)
      Or(
          Equals(t1, t2)
          And(not(ceil(t1) and p1 and s1), not(ceil(t2) and p2 and s2))
      )


Normalization of the compared terms is not implemented yet, so
Equals(a and b, b and a) will not be evaluated to Top.
-}
simplify
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Equals Sort (OrPattern variable)
    -> simplifier (Simplifiable variable)
simplify
    Equals { equalsFirst = first, equalsSecond = second }
  = do
    --traceM ("Equals.first=" ++ unlines (unparseToString <$> OrPattern.toPatterns first))
    --traceM ("Equals.second=" ++ unlines (unparseToString <$> OrPattern.toPatterns first))
    result <- simplifyEvaluated first second
    --traceM ("Equals.result=" ++ show result)
    return result

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Equals Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluated
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => OrPattern variable
    -> OrPattern variable
    -> simplifier (Simplifiable variable)
simplifyEvaluated first second
  | first == second = do
    --traceM ("simplifyEvaluated.1 " ++ show (length (show first)))
    return Simplifiable.top
  -- TODO: Maybe simplify equalities with top and bottom to ceil and floor
  | otherwise = do
    let isFunctionConditional Conditional {term} = isFunctionPattern term
    case (firstPatterns, secondPatterns) of
        ([firstP], [secondP]) -> do
            --traceM ("simplifyEvaluated.2 " ++ show (length (show first)))
            makeEvaluate firstP secondP
        ([firstP], _)
            | isFunctionConditional firstP -> do
                --traceM ("simplifyEvaluated.3 " ++ show (length (show first)))
                makeEvaluateFunctionalOr firstP secondPatterns
        (_, [secondP])
            | isFunctionConditional secondP -> do
                --traceM ("simplifyEvaluated.4 " ++ show (length (show first)))
                makeEvaluateFunctionalOr secondP firstPatterns
        _
            | OrPattern.isPredicate first && OrPattern.isPredicate second -> do
                --traceM ("simplifyEvaluated.5 " ++ show (length (show first)))
                return $
                    Unsimplified.mkIff
                        (Simplifiable.fromOrPattern first)
                        (Simplifiable.fromOrPattern second)
            | otherwise -> do
                --traceM ("simplifyEvaluated.6 " ++ show (length (show first)))
                makeEvaluate
                    (OrPattern.toPattern first)
                    (OrPattern.toPattern second)
  where
    firstPatterns = OrPattern.toPatterns first
    secondPatterns = OrPattern.toPatterns second

makeEvaluateFunctionalOr
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Pattern variable
    -> [Pattern variable]
    -> simplifier (Simplifiable variable)
makeEvaluateFunctionalOr first seconds = do
    Monad.when (length seconds == 1)
        (error . unlines $
            [ "Unexpected 'seconds' singleton."
            , "Please call makeEvaluate or switch the argument order."
            ]
        )
    let secondsWithCeils =
            map
                (\second ->
                    ( second
                    , Unsimplified.mkCeil (Simplifiable.fromPattern second)
                    )
                )
                seconds
        secondCeils = fmap snd secondsWithCeils
    firstEqualsSeconds <-
        mapM
            (makeEvaluateEqualsIfSecondNotBottom first)
            secondsWithCeils

    let firstCeil = Unsimplified.mkCeil (Simplifiable.fromPattern first)
        firstNotCeil = Unsimplified.mkNot firstCeil
        secondNotCeils = map Unsimplified.mkNot secondCeils
        oneNotBottom = Simplifiable.fromMultiOr (MultiOr.make secondCeils)
        allAreBottom =
            Simplifiable.fromMultiAnd
                (MultiAnd.make (firstNotCeil : secondNotCeils))
        oneIsNotBottomEquals =
            Simplifiable.fromMultiAnd
                (MultiAnd.make (firstCeil : oneNotBottom : firstEqualsSeconds))
    return
        (Unsimplified.mkOr
            allAreBottom
            oneIsNotBottomEquals
        )
  where
    makeEvaluateEqualsIfSecondNotBottom
        Conditional {term = firstTerm}
        (Conditional {term = secondTerm}, secondCeil)
      = do
        equality <- makeEvaluateTermsAssumesNoBottom firstTerm secondTerm
        return (Unsimplified.mkImplies secondCeil equality)

{-| evaluates an 'Equals' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    :: (GHC.HasCallStack, SimplifierVariable variable, MonadSimplify simplifier)
    => Pattern variable
    -> Pattern variable
    -> simplifier (Simplifiable variable)
makeEvaluate first second
  | first == second
  = do
    --traceM ("Equals.makeEvaluate.1 " ++ show (length (show first)))
    return Simplifiable.top
makeEvaluate
    first@Conditional { term = Top_ _ }
    second@Conditional { term = Top_ _ }
  = do
    --traceM ("Equals.makeEvaluate.2 " ++ show (length (show first)))
    return
        (Unsimplified.mkIff
            -- remove the sort.
            (Simplifiable.fromPattern first {term = mkTop_})
            -- remove the sort.
            (Simplifiable.fromPattern second {term = mkTop_})
        )
makeEvaluate
    Conditional
        { term = firstTerm
        , predicate = PredicateTrue
        , substitution = (Substitution.unwrap -> [])
        }
    Conditional
        { term = secondTerm
        , predicate = PredicateTrue
        , substitution = (Substitution.unwrap -> [])
        }
  = do
    --traceM ("Equals.makeEvaluate.3 " ++ show (length (show firstTerm)))
    makeEvaluateTerms firstTerm secondTerm
makeEvaluate
    first@Conditional { term = firstTerm }
    second@Conditional { term = secondTerm }
  = do
    --traceM ("Equals.makeEvaluate.4 " ++ show (length (show first)))
    termEquality <- makeEvaluateTermsAssumesNoBottom firstTerm secondTerm
    let firstCeil =
            (Unsimplified.mkCeil . Simplifiable.fromPattern)
                first { term = if termsAreEqual then mkTop_ else firstTerm }
        secondCeil =
            (Unsimplified.mkCeil . Simplifiable.fromPattern)
                second { term = if termsAreEqual then mkTop_ else secondTerm }
        termEqualityPattern =
            checkOrChange
                firstTerm
                secondTerm
                termEquality
                (WhenUnchanged (noSimplificationPossible firstTerm secondTerm))
                (WhenChanged termEquality)
    return $ Unsimplified.mkOr
        (Unsimplified.mkAnd
            termEqualityPattern
            (Unsimplified.mkAnd firstCeil secondCeil)
        )
        (Unsimplified.mkAnd
            (Unsimplified.mkNot firstCeil)
            (Unsimplified.mkNot secondCeil)
        )
  where
    termsAreEqual = firstTerm == secondTerm

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottom
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> TermLike variable
    -> simplifier (Simplifiable variable)
makeEvaluateTermsAssumesNoBottom firstTerm secondTerm = do
    result <-
        runMaybeT
        $ makeEvaluateTermsAssumesNoBottomMaybe firstTerm secondTerm
    (return . fromMaybe def) result
  where
    def = noSimplificationPossible firstTerm secondTerm

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottomMaybe
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> TermLike variable
    -> MaybeT simplifier (Simplifiable variable)
makeEvaluateTermsAssumesNoBottomMaybe first second = do
    result <- termEquals first second
    return (Simplifiable.fromOrCondition result)

{-| Combines two terms with 'Equals' into a predicate-substitution.

It does not attempt to fully simplify the terms (the not-ceil parts used to
catch the bottom=bottom case and everything above it), but, if the patterns are
total, this should not be needed anyway.
TODO(virgil): Fully simplify the terms (right now we're not simplifying not
because it returns an 'or').

See 'simplify' for detailed documentation.
-}
makeEvaluateTerms
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> TermLike variable
    -> simplifier (Simplifiable variable)
makeEvaluateTerms first second
  | first == second = return Simplifiable.top
  | otherwise = do
    result <- runMaybeT $ termEquals first second
    case result of
        Nothing -> return $ noSimplificationPossible first second
        Just predicatedOr -> do
            let ceilNegationAnd =
                    Unsimplified.mkAnd
                        (Unsimplified.mkNot
                            (Unsimplified.mkCeil
                                (Simplifiable.fromTermLike first)
                            )
                        )
                        (Unsimplified.mkNot
                            (Unsimplified.mkCeil
                                (Simplifiable.fromTermLike second)
                            )
                        )

            return $ checkOrConditionChange
                first
                second
                predicatedOr
                (WhenUnchanged (noSimplificationPossible first second))
                (WhenChanged
                    (Unsimplified.mkOr
                        (Simplifiable.fromOrCondition predicatedOr)
                        ceilNegationAnd
                    )
                )

{- | Simplify an equality relation of two patterns.

@termEquals@ assumes the result will be part of a predicate with a special
condition for testing @⊥ = ⊥@ equality.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

 -}
termEquals
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT simplifier (OrCondition variable)
termEquals first second = MaybeT $ do
    maybeResults <- BranchT.gather $ runMaybeT $ termEqualsAnd first second
    case sequence maybeResults of
        Nothing -> return Nothing
        Just results -> return $ Just $
            MultiOr.make (map Condition.eraseConditionalTerm results)

termEqualsAnd
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> MaybeT (BranchT simplifier) (Pattern variable)
termEqualsAnd p1 p2 =
    MaybeT $ run $ do
        notNormalized@Conditional {substitution} <- maybeTermEqualsWorker p1 p2
        let SubstitutionSimplifier { simplifySubstitution } =
                SubstitutionSimplifier.substitutionSimplifier
            replaceSubstitution
                :: Pattern variable -> Condition variable -> Pattern variable
            replaceSubstitution patt condition =
                patt {Conditional.substitution = mempty}
                `Condition.andCondition` condition
        orSubstitution <- simplifySubstitution substitution
        (Monad.Trans.lift . UnifierT.scatter)
            (replaceSubstitution notNormalized <$> orSubstitution)
  where
    run :: MaybeT (UnifierT (BranchT simplifier)) (Pattern variable)
        -> (BranchT simplifier) (Maybe (Pattern variable))
    run it = (runUnifierT . runMaybeT) it >>= either missingCase BranchT.scatter
    missingCase = const (return Nothing)

    maybeTermEqualsWorker
        :: forall unifier
        .  MonadUnify unifier
        => TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)
    maybeTermEqualsWorker = maybeTermEquals termEqualsAndWorker

    termEqualsAndWorker
        :: forall unifier
        .  MonadUnify unifier
        => TermLike variable
        -> TermLike variable
        -> unifier (Pattern variable)
    termEqualsAndWorker first second =
        either ignoreErrors scatterResults
        =<< (runUnifierT . runMaybeT) (maybeTermEqualsWorker first second)
      where
        ignoreErrors _ = return equalsPredicate
        scatterResults =
            maybe
                (return equalsPredicate) -- default if no results
                (BranchT.alternate . BranchT.scatter)
            . sequence
        equalsPredicate = noSimplificationPossiblePattern first second

newtype WhenChanged a = WhenChanged a
newtype WhenUnchanged a = WhenUnchanged a

checkOrChange
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Simplifiable variable
    -> WhenUnchanged a
    -> WhenChanged a
    -> a
checkOrChange
    first
    second
    maybeChanged
    whenUnchanged
    whenChanged@(WhenChanged defaultValue)
  =
    case Recursive.project maybeChanged of
        (Simplified orMaybeChanged) ->
            case OrPattern.toPatterns orMaybeChanged of
                [patt] ->
                    checkPatternChange
                        first second patt whenUnchanged whenChanged
                _ -> defaultValue
        (PartlySimplified orMaybeChanged) ->
            case OrPattern.toPatterns orMaybeChanged of
                [patt] ->
                    checkPatternChange
                        first second patt whenUnchanged whenChanged
                _ -> defaultValue
        (Unsimplified _) -> defaultValue

checkOrConditionChange
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> OrCondition variable
    -> WhenUnchanged a
    -> WhenChanged a
    -> a
checkOrConditionChange
    first
    second
    maybeChanged
    whenUnchanged
    whenChanged@(WhenChanged defaultValue)
  =
    case OrCondition.toConditions maybeChanged of
        [condition] ->
            checkConditionChange
                first second condition whenUnchanged whenChanged
        _ -> defaultValue

checkPatternChange
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Pattern variable
    -> WhenUnchanged a
    -> WhenChanged a
    -> a
checkPatternChange
    first
    second
    Conditional {term, predicate, substitution}
    whenUnchanged
    whenChanged@(WhenChanged defaultValue)
  | isTop predicate && Substitution.null substitution
  = termChecker term
  | isTop term && Substitution.null substitution
  = termChecker (Predicate.unwrapPredicate predicate)
  | otherwise = defaultValue
  where
    termChecker maybeTermChanged =
        checkTermChange
            first
            second
            maybeTermChanged
            whenUnchanged
            whenChanged

checkConditionChange
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Condition variable
    -> WhenUnchanged a
    -> WhenChanged a
    -> a
checkConditionChange
    first
    second
    Conditional {term = (), predicate, substitution}
    whenUnchanged
    whenChanged@(WhenChanged defaultValue)
  | Substitution.null substitution
  = termChecker (Predicate.unwrapPredicate predicate)
  | otherwise = defaultValue
  where
    termChecker maybeTermChanged =
        checkTermChange
            first
            second
            maybeTermChanged
            whenUnchanged
            whenChanged

checkTermChange
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
    -> WhenUnchanged a
    -> WhenChanged a
    -> a
checkTermChange
    first
    second
    maybeChanged
    (WhenUnchanged whenUnchanged)
    (WhenChanged whenChanged)
  =
    case maybeChanged of
        Equals_ _ _ t1 t2
            | (t1 == first && t2 == second)
                || (t2 == first && t1 == second) -> whenUnchanged
        _ -> whenChanged

noSimplificationPossibleCondition
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Condition variable
noSimplificationPossibleCondition first second =
    Condition.fromPredicate
    $ Predicate.markSimplified
    $ makeEqualsPredicate first second

noSimplificationPossible
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Simplifiable variable
noSimplificationPossible first second =
    Simplifiable.fromPredicate
    $ Predicate.markSimplified
    $ makeEqualsPredicate first second

noSimplificationPossiblePattern
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Pattern variable
noSimplificationPossiblePattern first second =
    Pattern.fromCondition (noSimplificationPossibleCondition first second)
