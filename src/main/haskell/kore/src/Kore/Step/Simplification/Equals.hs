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
    , simplify
    ) where

import Data.Maybe
       ( fromMaybe, isNothing )
import Data.Reflection
       ( give )

import           Kore.AST.Common
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
                 ( pattern PredicateTrue, makeEqualsPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, toExpandedPattern )
import qualified Kore.Step.Simplification.And as And
                 ( simplifyEvaluated )
import qualified Kore.Step.Simplification.AndTerms as AndTerms
                 ( termEquals )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate )
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
    + If the first term is a Variable and the second is functional,
      then we get a substitution:
        Or(
            And(
                [t1 = t2]
                And(p1 and s1, p2 and s2))
            And(not(p1 and s1), not(p2 and s2))
        )
    + If the terms are Top, this becomes
      Equals(p1 and s1, p2 and s2) = Iff(p1 and s1, p2 and s2)
    + If the predicate and substitution are Top, then the result is just
      Equals(t1, t2)

Normalization of the compared terms is not implemented yet, so
Equals(a and b, b and a) will not be evaluated to Top.
-}
simplify
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> Equals level (OrOfExpandedPattern level Variable)
    -> Simplifier
        ( OrOfExpandedPattern level Variable
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
        )
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level Variable
    -> OrOfExpandedPattern level Variable
    -> Simplifier
        (OrOfExpandedPattern level Variable, SimplificationProof level)
simplifyEvaluated tools first second
  | first == second =
    return (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  -- TODO: Maybe simplify equalities with top and bottom to ceil and floor
  | otherwise =
    case ( firstPatterns, secondPatterns )
      of
        ([firstP], [secondP]) -> makeEvaluate tools firstP secondP
        _ ->
            give (MetadataTools.sortTools tools)
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
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level Variable
    -> ExpandedPattern level Variable
    -> Simplifier
        (OrOfExpandedPattern level Variable, SimplificationProof level)
makeEvaluate
    tools
    first@ExpandedPattern
        { term = Top_ _ }
    second@ExpandedPattern
        { term = Top_ _ }
  =
    let
        (result, _proof) = give (MetadataTools.sortTools tools )
            $ Iff.makeEvaluate first second
    in
        return (result, SimplificationProof)
makeEvaluate
    tools
    ExpandedPattern
        { term = firstTerm
        , predicate = PredicateTrue
        , substitution = []
        }
    ExpandedPattern
        { term = secondTerm
        , predicate = PredicateTrue
        , substitution = []
        }
  | isNothing maybeSimplified
  = return
        (OrOfExpandedPattern.make
            [ ExpandedPattern
                { term = mkTop
                , predicate = give (MetadataTools.sortTools tools)
                    $ makeEqualsPredicate firstTerm secondTerm
                , substitution = []
                }
            ]
        , SimplificationProof
        )
  where
    maybeSimplified =
        makeEvaluateTermsAssumesNoBottomMaybe tools firstTerm secondTerm
makeEvaluate
    tools
    first@ExpandedPattern
        { term = firstTerm }
    second@ExpandedPattern
        { term = secondTerm }
  = do
    let
        (firstCeil, _proof1) =
            Ceil.makeEvaluate tools
                first
                    { ExpandedPattern.term =
                        if termsAreEqual then mkTop else firstTerm
                    }
        (secondCeil, _proof2) =
            Ceil.makeEvaluate tools
                second
                    { ExpandedPattern.term =
                        if termsAreEqual then mkTop else secondTerm
                    }
        (firstCeilNegation, _proof3) =
            give sortTools $ Not.simplifyEvaluated firstCeil
        (secondCeilNegation, _proof4) =
            give sortTools $ Not.simplifyEvaluated secondCeil
    (termEquality, _proof) <-
        makeEvaluateTermsAssumesNoBottom tools firstTerm secondTerm
    (negationAnd, _proof) <-
        And.simplifyEvaluated tools firstCeilNegation secondCeilNegation
    (ceilAnd, _proof) <- And.simplifyEvaluated tools firstCeil secondCeil
    (equalityAnd, _proof) <-
        And.simplifyEvaluated tools termEquality ceilAnd
    let
        (finalOr, _proof) =
            give sortTools $ Or.simplifyEvaluated equalityAnd negationAnd
    return (finalOr, SimplificationProof)
  where
    sortTools = MetadataTools.sortTools tools
    termsAreEqual = firstTerm == secondTerm

-- Do not export this. This not valid as a standalone function, it
-- assumes that some extra conditions will be added on the outside
makeEvaluateTermsAssumesNoBottom
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> Simplifier
        (OrOfExpandedPattern level Variable, SimplificationProof level)
makeEvaluateTermsAssumesNoBottom
    tools
    firstTerm
    secondTerm
  =
    fromMaybe
        (return
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = mkTop
                    , predicate = give (MetadataTools.sortTools tools)
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
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level Variable
    -> PureMLPattern level Variable
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level Variable, SimplificationProof level)
        )
makeEvaluateTermsAssumesNoBottomMaybe tools first second =
    give tools $ do  -- Maybe monad
        result <- AndTerms.termEquals tools first second
        return $ do -- Simplifier monad
            (patt, _proof) <- result
            return
                ( OrOfExpandedPattern.make [ patt ]
                , SimplificationProof
                )
