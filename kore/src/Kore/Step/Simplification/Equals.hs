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
    , makeEvaluateTermsToPredicate
    , simplify
    ) where

import Control.Error
       ( MaybeT (..) )
import Control.Monad
       ( foldM )
import Data.List
       ( foldl' )
import Data.Maybe
       ( fromMaybe )

import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
import           Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeAndPredicate,
                 makeEqualsPredicate, makeNotPredicate )
import           Kore.Step.RecursiveAttributes
                 ( isFunctionPattern )
import qualified Kore.Step.Simplification.And as And
                 ( simplifyEvaluated )
import qualified Kore.Step.Simplification.AndTerms as AndTerms
                 ( termEquals )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, makeEvaluateTerm )
import           Kore.Step.Simplification.Data as Simplifier hiding
                 ( Equals )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( makeEvaluate )
import qualified Kore.Step.Simplification.Implies as Implies
                 ( simplifyEvaluated )
import qualified Kore.Step.Simplification.Not as Not
                 ( simplifyEvaluated )
import qualified Kore.Step.Simplification.Or as Or
                 ( simplifyEvaluated )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Fresh

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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => Equals Sort (OrPattern variable)
    -> Simplifier (OrPattern variable)
simplify Equals { equalsFirst = first, equalsSecond = second } =
    simplifyEvaluated first second

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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => OrPattern variable
    -> OrPattern variable
    -> Simplifier (OrPattern variable)
simplifyEvaluated
    first
    second
  | first == second = return OrPattern.top
  -- TODO: Maybe simplify equalities with top and bottom to ceil and floor
  | otherwise = do
    tools <- Simplifier.askMetadataTools
    let isFunctionConditional Conditional {term} = isFunctionPattern tools term
    case (firstPatterns, secondPatterns) of
        ([firstP], [secondP]) -> makeEvaluate firstP secondP
        ([firstP], _)
            | isFunctionConditional firstP ->
                makeEvaluateFunctionalOr firstP secondPatterns
        (_, [secondP])
            | isFunctionConditional secondP ->
                makeEvaluateFunctionalOr secondP firstPatterns
        _ ->
            makeEvaluate
                (OrPattern.toPattern first)
                (OrPattern.toPattern second)
  where
    firstPatterns = MultiOr.extractPatterns first
    secondPatterns = MultiOr.extractPatterns second

makeEvaluateFunctionalOr
    :: forall variable .
        ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => Pattern variable
    -> [Pattern variable]
    -> Simplifier (OrPattern variable)
makeEvaluateFunctionalOr first seconds = do
    firstCeil <- Ceil.makeEvaluate first
    secondCeilsWithProofs <- mapM Ceil.makeEvaluate seconds
    firstNotCeil <- Not.simplifyEvaluated firstCeil
    let secondCeils = secondCeilsWithProofs
    secondNotCeils <- traverse Not.simplifyEvaluated secondCeils
    let oneNotBottom = foldl' Or.simplifyEvaluated OrPattern.bottom secondCeils
    allAreBottom <-
        foldM
            And.simplifyEvaluated
            (OrPattern.fromPatterns [Pattern.top])
            (firstNotCeil : secondNotCeils)
    firstEqualsSeconds <-
        mapM
            (makeEvaluateEqualsIfSecondNotBottom first)
            (zip seconds secondCeils)
    oneIsNotBottomEquals <-
        foldM
            And.simplifyEvaluated
            firstCeil
            (oneNotBottom : firstEqualsSeconds)
    return (MultiOr.merge allAreBottom oneIsNotBottomEquals)
  where
    makeEvaluateEqualsIfSecondNotBottom
        Conditional {term = firstTerm}
        (Conditional {term = secondTerm}, secondCeil)
      = do
        substitutionSimplifier <- Simplifier.askSimplifierPredicate
        simplifier <- Simplifier.askSimplifierTermLike
        axiomIdToSimplfier <- Simplifier.askSimplifierAxioms
        equality <- makeEvaluateTermsAssumesNoBottom firstTerm secondTerm
        result <-
            Implies.simplifyEvaluated
                substitutionSimplifier
                simplifier
                axiomIdToSimplfier
                secondCeil
                equality
        return result

{-| evaluates an 'Equals' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => Pattern variable
    -> Pattern variable
    -> Simplifier (OrPattern variable)
makeEvaluate
    first@Conditional { term = Top_ _ }
    second@Conditional { term = Top_ _ }
  =
    return (Iff.makeEvaluate first second)
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
    result <- makeEvaluateTermsToPredicate firstTerm secondTerm
    return (Pattern.fromPredicate <$> result)

makeEvaluate
    first@Conditional { term = firstTerm }
    second@Conditional { term = secondTerm }
  = do
    let first' = first { term = if termsAreEqual then mkTop_ else firstTerm }
    firstCeil <- Ceil.makeEvaluate first'
    let second' = second { term = if termsAreEqual then mkTop_ else secondTerm }
    secondCeil <- Ceil.makeEvaluate second'
    firstCeilNegation <- Not.simplifyEvaluated firstCeil
    secondCeilNegation <- Not.simplifyEvaluated secondCeil
    termEquality <- makeEvaluateTermsAssumesNoBottom firstTerm secondTerm
    negationAnd <- And.simplifyEvaluated firstCeilNegation secondCeilNegation
    ceilAnd <- And.simplifyEvaluated firstCeil secondCeil
    equalityAnd <- And.simplifyEvaluated termEquality ceilAnd
    return $ Or.simplifyEvaluated equalityAnd negationAnd
  where
    termsAreEqual = firstTerm == secondTerm

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottom
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => TermLike variable
    -> TermLike variable
    -> Simplifier (OrPattern variable)
makeEvaluateTermsAssumesNoBottom firstTerm secondTerm = do
    result <-
        runMaybeT
        $ makeEvaluateTermsAssumesNoBottomMaybe firstTerm secondTerm
    (return . fromMaybe def) result
  where
    def =
        OrPattern.fromPattern
            Conditional
                { term = mkTop_
                , predicate = makeEqualsPredicate firstTerm secondTerm
                , substitution = mempty
                }

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottomMaybe
    :: forall variable .
        ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => TermLike variable
    -> TermLike variable
    -> MaybeT Simplifier (OrPattern variable)
makeEvaluateTermsAssumesNoBottomMaybe first second = do
    result <- AndTerms.termEquals first second
    return (Pattern.fromPredicate <$> result)

{-| Combines two terms with 'Equals' into a predicate-substitution.

It does not attempt to fully simplify the terms (the not-ceil parts used to
catch the bottom=bottom case and everything above it), but, if the patterns are
total, this should not be needed anyway.
TODO(virgil): Fully simplify the terms (right now we're not simplifying not
because it returns an 'or').

See 'simplify' for detailed documentation.
-}
makeEvaluateTermsToPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => TermLike variable
    -> TermLike variable
    -> Simplifier (OrPredicate variable)
makeEvaluateTermsToPredicate first second
  | first == second = return OrPredicate.top
  | otherwise = do
    result <- runMaybeT $ AndTerms.termEquals first second
    case result of
        Nothing ->
            return
                $ OrPredicate.fromPredicate
                $ Predicate.fromPredicate
                $ makeEqualsPredicate first second
        Just predicatedOr -> do
            firstCeilOr <- Ceil.makeEvaluateTerm first
            secondCeilOr <- Ceil.makeEvaluateTerm second
            let
                toPredicateSafe
                    ps@Conditional {term = (), predicate, substitution}
                  | Substitution.null substitution =
                    predicate
                  | otherwise =
                    error
                        (  "Unimplemented: we should split the configuration"
                        ++ " for or with nonempty substitution."
                        ++ " input=" ++ show ps
                        ++ ", first=" ++ show first
                        ++ ", second=" ++ show second
                        )
                firstCeil =
                    OrPredicate.toPredicate (fmap toPredicateSafe firstCeilOr)
                secondCeil =
                    OrPredicate.toPredicate (fmap toPredicateSafe secondCeilOr)
                firstCeilNegation = makeNotPredicate firstCeil
                secondCeilNegation = makeNotPredicate secondCeil
                ceilNegationAnd =
                    makeAndPredicate firstCeilNegation secondCeilNegation
            return $ MultiOr.merge
                predicatedOr
                (OrPredicate.fromPredicate
                    $ Predicate.fromPredicate ceilNegationAnd
                )
