{-|
Module      : Kore.Step.Simplification.Not
Description : Tools for Not pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Not
    ( makeEvaluate
    , simplify
    , simplifyEvaluated
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive

import           Kore.AST.Pure
import           Kore.AST.Valid hiding
                 ( mkAnd )
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeNotPredicate, makeTruePredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
import qualified Kore.Step.Simplification.And as And
import           Kore.Step.Simplification.Data
                 ( BranchT, PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier, gather )
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-|'simplify' simplifies a 'Not' pattern with an 'OrOfExpandedPattern'
child.

Right now this uses the following:

* not top = bottom
* not bottom = top

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
    -> Not Object (OrOfExpandedPattern Object variable)
    -> Simplifier (OrOfExpandedPattern Object variable)
simplify
    tools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers
    Not { notChild = child }
  =
    gather $ simplifyEvaluated
        tools
        predicateSimplifier
        termSimplifier
        axiomSimplifiers
        child

{-|'simplifyEvaluated' simplifies a 'Not' pattern given its
'OrOfExpandedPattern' child.

See 'simplify' for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Not level) (Valid level) (OrOfExpandedPattern level variable)

instead of an 'OrOfExpandedPattern' argument. The type of 'makeEvaluate' may
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
    -> BranchT Simplifier (ExpandedPattern Object variable)
simplifyEvaluated
    tools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers
    simplified
  | OrOfExpandedPattern.isFalse simplified =
    return ExpandedPattern.top
  | OrOfExpandedPattern.isTrue simplified =
    empty
  | otherwise =
    Foldable.foldrM mkAnd ExpandedPattern.top (simplified >>= makeEvaluate)
  where
    mkAnd =
        And.makeEvaluate
            tools
            predicateSimplifier
            termSimplifier
            axiomSimplifiers

{-|'makeEvaluate' simplifies a 'Not' pattern given its 'ExpandedPattern'
child.

See 'simplify' for details.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> OrOfExpandedPattern level variable
makeEvaluate Predicated { term, predicate, substitution } =
    MultiOr.make
        [ Predicated
            { term = makeTermNot term
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        , Predicated
            { term = mkTop (getSort term)
            , predicate =
                makeNotPredicate
                $ makeAndPredicate predicate
                $ Predicate.fromSubstitution substitution
            , substitution = mempty
            }
        ]

makeTermNot
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => StepPattern level variable
    -> StepPattern level variable
-- TODO: maybe other simplifications like
-- not ceil = floor not
-- not forall = exists not
makeTermNot term@(Recursive.project -> _ :< projected)
  | BottomPattern _ <- projected = mkTop (getSort term)
  | TopPattern _ <- projected = mkBottom (getSort term)
  | otherwise = mkNot term
