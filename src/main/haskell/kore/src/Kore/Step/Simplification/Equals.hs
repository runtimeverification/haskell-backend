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
    , makeEvaluateTermsToPredicateSubstitution
    , simplify
    ) where

import Data.Maybe
       ( fromMaybe )
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( Equals (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, pattern PredicateTrue,
                 makeAndPredicate, makeEqualsPredicate, makeNotPredicate,
                 makeOrPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, toExpandedPattern )
import           Kore.Step.PredicateSubstitution
                 ( PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( PredicateSubstitution (..), top )
import qualified Kore.Step.Simplification.And as And
                 ( simplifyEvaluated )
import qualified Kore.Step.Simplification.AndTerms as AndTerms
                 ( termEquals )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..), Simplifier )
import qualified Kore.Step.Simplification.Iff as Iff
                 ( makeEvaluate )
import qualified Kore.Step.Simplification.Not as Not
                 ( simplifyEvaluated )
import qualified Kore.Step.Simplification.Or as Or
                 ( simplifyEvaluated )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh

{-|'simplify' simplifies an 'Equals' pattern made of 'OrOfExpandedPattern's.

This uses the following simplifications
(t = term, s = substitution, p = predicate):

* Equals(a, a) = true
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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> Equals level (OrOfExpandedPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    Equals
        { equalsFirst = first
        , equalsSecond = second
        }
  =
    simplifyEvaluated tools first second

simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated tools first second
  | first == second =
    return (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  -- TODO: Maybe simplify equalities with top and bottom to ceil and floor
  | otherwise =
    case ( firstPatterns, secondPatterns )
      of
        ([firstP], [secondP]) -> makeEvaluate tools firstP secondP
        _ ->
            give (MetadataTools.symbolOrAliasSorts tools)
                $ makeEvaluate tools
                    (OrOfExpandedPattern.toExpandedPattern first)
                    (OrOfExpandedPattern.toExpandedPattern second)
  where
    firstPatterns = OrOfExpandedPattern.extractPatterns first
    secondPatterns = OrOfExpandedPattern.extractPatterns second

{-| evaluates an 'Equals' given its two 'ExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate
    tools
    first@Predicated
        { term = Top_ _ }
    second@Predicated
        { term = Top_ _ }
  =
    let
        (result, _proof) = give (MetadataTools.symbolOrAliasSorts tools )
            $ Iff.makeEvaluate first second
    in
        return (result, SimplificationProof)
makeEvaluate
    tools
    Predicated
        { term = firstTerm
        , predicate = PredicateTrue
        , substitution = []
        }
    Predicated
        { term = secondTerm
        , predicate = PredicateTrue
        , substitution = []
        }
  = do
    (result, _proof) <-
        makeEvaluateTermsToPredicateSubstitution tools firstTerm secondTerm
    case result of
        PredicateSubstitution {predicate = PredicateFalse} ->
            return (OrOfExpandedPattern.make [], SimplificationProof)
        PredicateSubstitution {predicate, substitution} ->
            return
                (OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop
                        , predicate = predicate
                        , substitution = substitution
                        }
                    ]
                , SimplificationProof
                )
makeEvaluate
    tools
    first@Predicated
        { term = firstTerm }
    second@Predicated
        { term = secondTerm }
  = do
    let
        (firstCeil, _proof1) =
            Ceil.makeEvaluate tools
                first
                    { term =
                        if termsAreEqual then mkTop else firstTerm
                    }
        (secondCeil, _proof2) =
            Ceil.makeEvaluate tools
                second
                    { term =
                        if termsAreEqual then mkTop else secondTerm
                    }
        (firstCeilNegation, _proof3) =
            give symbolOrAliasSorts $ Not.simplifyEvaluated firstCeil
        (secondCeilNegation, _proof4) =
            give symbolOrAliasSorts $ Not.simplifyEvaluated secondCeil
    (termEquality, _proof) <-
        makeEvaluateTermsAssumesNoBottom tools firstTerm secondTerm
    (negationAnd, _proof) <-
        And.simplifyEvaluated tools firstCeilNegation secondCeilNegation
    (ceilAnd, _proof) <- And.simplifyEvaluated tools firstCeil secondCeil
    (equalityAnd, _proof) <-
        And.simplifyEvaluated tools termEquality ceilAnd
    let
        (finalOr, _proof) =
            give symbolOrAliasSorts $ Or.simplifyEvaluated equalityAnd negationAnd
    return (finalOr, SimplificationProof)
  where
    symbolOrAliasSorts = MetadataTools.symbolOrAliasSorts tools
    termsAreEqual = firstTerm == secondTerm

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottom
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateTermsAssumesNoBottom
    tools
    firstTerm
    secondTerm
  =
    fromMaybe
        (return
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkTop
                    , predicate = give (MetadataTools.symbolOrAliasSorts tools)
                        $ makeEqualsPredicate firstTerm secondTerm
                    , substitution = []
                    }
                ]
            , SimplificationProof
            )
        )
        (makeEvaluateTermsAssumesNoBottomMaybe tools firstTerm secondTerm)

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottomMaybe
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level variable, SimplificationProof level)
        )
makeEvaluateTermsAssumesNoBottomMaybe tools first second =
    give tools $ do  -- Maybe monad
        result <- AndTerms.termEquals tools first second
        return $ do -- Simplifier monad
            (PredicateSubstitution {predicate, substitution}, _proof) <- result
            return
                ( OrOfExpandedPattern.make
                    [ Predicated
                        { term = mkTop
                        , predicate = predicate
                        , substitution = substitution
                        }
                    ]
                , SimplificationProof
                )

{-| Combines two terms with 'Equals' into a predicate-substitution.

It does not attempt to fully simplify the terms (the not-ceil parts used to
catch the bottom=bottom case and everything above it), but, if the patterns are
total, this should not be needed anyway.
TODO(virgil): Fully simplify the terms (right now we're not simplifying not
because it returns an 'or').

See 'simplify' for detailed documentation.
-}
makeEvaluateTermsToPredicateSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Simplifier
        (PredicateSubstitution level variable, SimplificationProof level)
makeEvaluateTermsToPredicateSubstitution tools first second
  | first == second =
    return
        ( PredicateSubstitution.top
        , SimplificationProof
        )
  | otherwise = give symbolOrAliasSorts $
    case AndTerms.termEquals tools first second of
        Nothing -> return
            ( PredicateSubstitution
                { predicate = makeEqualsPredicate first second
                , substitution = []
                }
            , SimplificationProof
            )
        Just wrappedResult -> do
            (PredicateSubstitution {predicate, substitution}, _proof) <-
                wrappedResult
            let
                (firstCeil, _proof1) = Ceil.makeEvaluateTerm tools first
                (secondCeil, _proof2) = Ceil.makeEvaluateTerm tools second
                (firstCeilNegation, _proof3) = makeNotPredicate firstCeil
                (secondCeilNegation, _proof4) = makeNotPredicate secondCeil
                (ceilNegationAnd, _proof5) =
                    makeAndPredicate firstCeilNegation secondCeilNegation
                (finalPredicate, _proof6) =
                    makeOrPredicate predicate ceilNegationAnd
            return
                ( PredicateSubstitution
                    { predicate = finalPredicate
                    , substitution = substitution
                    }
                , SimplificationProof
                )
  where
    symbolOrAliasSorts = MetadataTools.symbolOrAliasSorts tools

