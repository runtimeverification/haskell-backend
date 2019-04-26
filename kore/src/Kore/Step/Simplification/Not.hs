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

import qualified Data.Foldable as Foldable

import           Kore.AST.Common
                 ( Not (..) )
import           Kore.AST.Valid hiding
                 ( mkAnd )
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeNotPredicate, makeTruePredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern as Pattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
import qualified Kore.Step.Simplification.And as And
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier, gather )
import           Kore.Step.TermLike
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
    => SmtMetadataTools Attribute.Symbol
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
    simplifyEvaluated
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
    => SmtMetadataTools Attribute.Symbol
    -> PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -> OrOfExpandedPattern Object variable
    -> Simplifier (OrOfExpandedPattern Object variable)
simplifyEvaluated
    tools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers
    simplified
  | OrOfExpandedPattern.isFalse simplified =
    return (MultiOr.make [Pattern.top])
  | OrOfExpandedPattern.isTrue simplified =
    return (MultiOr.make [])
  | otherwise =
    fmap MultiOr.make . gather
    $ Foldable.foldrM mkAnd Pattern.top (simplified >>= makeEvaluate)
  where
    mkAnd =
        And.makeEvaluate
            tools
            predicateSimplifier
            termSimplifier
            axiomSimplifiers

{-|'makeEvaluate' simplifies a 'Not' pattern given its 'Pattern'
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
    => Pattern level variable
    -> OrOfExpandedPattern level variable
makeEvaluate Conditional { term, predicate, substitution } =
    MultiOr.make
        [ Conditional
            { term = makeTermNot term
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        , Conditional
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
    => TermLike variable
    -> TermLike variable
-- TODO: maybe other simplifications like
-- not ceil = floor not
-- not forall = exists not
makeTermNot term
  | isBottom term = mkTop    (getSort term)
  | isTop term    = mkBottom (getSort term)
  | otherwise = mkNot term
