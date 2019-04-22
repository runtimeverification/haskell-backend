{-|
Module      : Kore.Step.Simplification.Implies
Description : Tools for Implies pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Implies
    ( simplify
    , simplifyEvaluated
    ) where

import qualified Data.Functor.Foldable as Recursive

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeImpliesPredicate, makeTruePredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), substitutionToPredicate )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier, gather )
import qualified Kore.Step.Simplification.Not as Not
                 ( makeEvaluate, simplifyEvaluated )
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-|'simplify' simplifies an 'Implies' pattern with 'OrOfExpandedPattern'
children.

Right now this uses the following simplifications:

* a -> (b or c) = (a -> b) or (a -> c)
* bottom -> b = top
* top -> b = b
* a -> top = top
* a -> bottom = not a

and it has a special case for children with top terms.
-}
simplify
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => MetadataTools Object Attribute.Symbol
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -> Implies Object (OrOfExpandedPattern Object variable)
    -> Simplifier
        (OrOfExpandedPattern Object variable , SimplificationProof Object)
simplify
    tools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers
    Implies
        { impliesFirst = first
        , impliesSecond = second
        }
  =
    simplifyEvaluated
        tools
        predicateSimplifier
        termSimplifier
        axiomSimplifiers
        first
        second

{-| simplifies an Implies given its two 'OrOfExpandedPattern' children.

See 'simplify' for details.
-}
-- TODO: Maybe transform this to (not a) \/ b
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Implies level) (Valid level) (OrOfExpandedPattern level variable)

instead of two 'OrOfExpandedPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluated
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => MetadataTools Object Attribute.Symbol
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -> OrOfExpandedPattern Object variable
    -> OrOfExpandedPattern Object variable
    -> Simplifier
        (OrOfExpandedPattern Object variable, SimplificationProof Object)
simplifyEvaluated
    tools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers
    first
    second
  | OrOfExpandedPattern.isTrue first =
    return (second, SimplificationProof)
  | OrOfExpandedPattern.isFalse first =
    return (MultiOr.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isTrue second =
    return (MultiOr.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isFalse second = do
    result <-
        gather $ Not.simplifyEvaluated
            tools
            predicateSimplifier
            termSimplifier
            axiomSimplifiers
            first
    return (result, SimplificationProof)
  | otherwise = do
    results <- traverse (simplifyEvaluateHalfImplies' first) second
    return (MultiOr.flatten results, SimplificationProof)
  where
    simplifyEvaluateHalfImplies' =
        simplifyEvaluateHalfImplies
            tools
            predicateSimplifier
            termSimplifier
            axiomSimplifiers

simplifyEvaluateHalfImplies
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => MetadataTools Object Attribute.Symbol
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -> OrOfExpandedPattern Object variable
    -> ExpandedPattern Object variable
    -> Simplifier (OrOfExpandedPattern Object variable)
simplifyEvaluateHalfImplies
    tools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers
    first
    second
  | OrOfExpandedPattern.isTrue first =
    return (MultiOr.make [second])
  | OrOfExpandedPattern.isFalse first =
    return (MultiOr.make [ExpandedPattern.top])
  | ExpandedPattern.isTop second =
    return (MultiOr.make [ExpandedPattern.top])
  | ExpandedPattern.isBottom second =
    gather $ Not.simplifyEvaluated
        tools
        predicateSimplifier
        termSimplifier
        axiomSimplifiers
        first
  | otherwise =
    -- TODO: Also merge predicate-only patterns for 'Or'
    return $ case MultiOr.extractPatterns first of
        [firstP] -> makeEvaluateImplies firstP second
        _ ->
            makeEvaluateImplies
                (OrOfExpandedPattern.toExpandedPattern first)
                second

makeEvaluateImplies
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> OrOfExpandedPattern level variable
makeEvaluateImplies
    first second
  | ExpandedPattern.isTop first =
    MultiOr.make [second]
  | ExpandedPattern.isBottom first =
    MultiOr.make [ExpandedPattern.top]
  | ExpandedPattern.isTop second =
    MultiOr.make [ExpandedPattern.top]
  | ExpandedPattern.isBottom second =
    Not.makeEvaluate first
  | otherwise =
    makeEvaluateImpliesNonBool first second

makeEvaluateImpliesNonBool
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> OrOfExpandedPattern level variable
makeEvaluateImpliesNonBool
    pattern1@Predicated
        { term = firstTerm
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    pattern2@Predicated
        { term = secondTerm
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  | (Recursive.project -> _ :< TopPattern _) <- firstTerm
  , (Recursive.project -> _ :< TopPattern _) <- secondTerm
  =
    MultiOr.make
        [ Predicated
            { term = firstTerm
            , predicate =
                makeImpliesPredicate
                    (makeAndPredicate
                        firstPredicate
                        (substitutionToPredicate firstSubstitution))
                    (makeAndPredicate
                        secondPredicate
                        (substitutionToPredicate secondSubstitution)
                    )
            , substitution = mempty
            }
        ]
  | otherwise =
    MultiOr.make
        [ Predicated
            { term =
                mkImplies
                    (ExpandedPattern.toMLPattern pattern1)
                    (ExpandedPattern.toMLPattern pattern2)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
