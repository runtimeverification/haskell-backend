{-|
Module      : Kore.Step.Simplification.And
Description : Tools for And pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.And
    ( makeEvaluate
    , simplify
    , simplifyEvaluated
    ) where

import Data.List
       ( foldl1', nub )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom, isBottom, isTop )
import           Kore.Step.Function.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( crossProductGenericF, filterOr, isFalse, isTrue, make )
import           Kore.Step.Pattern
import qualified Kore.Step.Simplification.AndTerms as AndTerms
                 ( termAnd )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-|'simplify' simplifies an 'And' of 'OrOfExpandedPattern'.

To do that, it first distributes the terms, making it an Or of And patterns,
each And having 'ExpandedPattern's as children, then it simplifies each of
those.

Since an ExpandedPattern is of the form term /\ predicate /\ substitution,
making an and between two ExpandedPatterns roughly means and-ing each of their
components separately.

This means that a bottom component anywhere makes the result bottom, while
top can always be ignored.

When we 'and' two terms:
by Proposition 5.24 from (1),
    x and functional-pattern = functional-pattern and [x=phi]
We can generalize that to:
    x and function-pattern
        = function-pattern and ceil(function-pattern) and [x=phi]
        but note that ceil(function-pattern) is not actually needed.
We can still generalize that to:
    function-like-pattern1 and function-like-pattern2
        = function-pattern1 and function-pattern1 == function-pattern2
Also, we have
    constructor1(s1, ..., sk) and constructor2(t1, ..., tk):
        if constructor1 != constructor2 then this is bottom
        else it is
            constructor1(s1 and t1, ..., sk and tk)
    * constructor - 'inj' (sort injection) pairs become bottom
    * injection-injection pairs with the same injection work the same as
      identical constructors
    domain-value1 and domain-value1, where both are string-based:
        domain-value1 if they are equal
        bottom otherwise
    the same for two string literals and two chars
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> And level (OrOfExpandedPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    And
        { andFirst = first
        , andSecond = second
        }
  =
    simplifyEvaluated
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        first
        second

{-| simplifies an And given its two 'OrOfExpandedPattern' children.

See 'simplify' for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (And level) (Valid level) (OrOfExpandedPattern level variable)

instead of two 'OrOfExpandedPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    first
    second
  | OrOfExpandedPattern.isFalse first =
    return (OrOfExpandedPattern.make [], SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    return (OrOfExpandedPattern.make [], SimplificationProof)

  | OrOfExpandedPattern.isTrue first =
    return (second, SimplificationProof)
  | OrOfExpandedPattern.isTrue second =
    return (first, SimplificationProof)

  | otherwise = do
    orWithProof <-
        OrOfExpandedPattern.crossProductGenericF
            (makeEvaluate
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
            )
            first
            second
    return
        -- TODO: It's not obvious at all when filtering occurs and when it
        -- doesn't.
        ( OrOfExpandedPattern.filterOr
            -- TODO: Remove fst.
            (fst <$> orWithProof)
        , SimplificationProof
        )

{-|'makeEvaluate' simplifies an 'And' of 'ExpandedPattern's.

See the comment for 'simplify' to find more details.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
makeEvaluate
    tools substitutionSimplifier simplifier axiomIdToSimplifier first second
  | ExpandedPattern.isBottom first || ExpandedPattern.isBottom second =
    return (ExpandedPattern.bottom, SimplificationProof)
  | ExpandedPattern.isTop first =
    return (second, SimplificationProof)
  | ExpandedPattern.isTop second =
    return (first, SimplificationProof)
  | otherwise =
    makeEvaluateNonBool
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        first
        second

makeEvaluateNonBool
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBool
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Predicated
        { term = firstTerm
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    Predicated
        { term = secondTerm
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  = do -- IntCounter monad
    ( Predicated
            { term = termTerm
            , predicate = termPredicate
            , substitution = termSubstitution
            }
        , _proof
        ) <- makeTermAnd
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            firstTerm
            secondTerm
    (   Predicated
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _proof
        ) <- mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            [firstPredicate, secondPredicate, termPredicate]
            [firstSubstitution, secondSubstitution, termSubstitution]
    return
        ( Predicated
            { term = applyAndIdempotence termTerm
            , predicate = applyAndIdempotence <$> mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )

applyAndIdempotence
    ::  ( Ord (variable level)
        , MetaOrObject level
        , Show (variable level)
        , Unparse (variable level)
        , SortedVariable variable
        )
    => StepPattern level variable
    -> StepPattern level variable
applyAndIdempotence patt =
    foldl1' mkAnd (nub (children patt))
  where
    children (And_ _ p1 p2) = children p1 ++ children p2
    children p = [p]

makeTermAnd
    ::  ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> StepPattern level variable
    -> StepPattern level variable
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
makeTermAnd = AndTerms.termAnd
