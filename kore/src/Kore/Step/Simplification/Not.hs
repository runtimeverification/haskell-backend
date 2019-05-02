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

import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike hiding
                 ( mkAnd )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeNotPredicate, makeTruePredicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Simplification.And as And
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier,
                 gather )
import           Kore.Syntax.Not
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-|'simplify' simplifies a 'Not' pattern with an 'OrPattern'
child.

Right now this uses the following:

* not top = bottom
* not bottom = top

-}
simplify
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> Not Sort (OrPattern variable)
    -> Simplifier (OrPattern variable)
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
'OrPattern' child.

See 'simplify' for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Not Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of an 'OrPattern' argument. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluated
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => SmtMetadataTools Attribute.Symbol
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> OrPattern variable
    -> Simplifier (OrPattern variable)
simplifyEvaluated
    tools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers
    simplified
  | OrPattern.isFalse simplified = return (OrPattern.fromPatterns [Pattern.top])
  | OrPattern.isTrue  simplified = return (OrPattern.fromPatterns [])
  | otherwise =
    fmap OrPattern.fromPatterns . gather
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
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern variable
    -> OrPattern variable
makeEvaluate Conditional { term, predicate, substitution } =
    OrPattern.fromPatterns
        [ Conditional
            { term = makeTermNot term
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        , Conditional
            { term = mkTop (termLikeSort term)
            , predicate =
                makeNotPredicate
                $ makeAndPredicate predicate
                $ Predicate.fromSubstitution substitution
            , substitution = mempty
            }
        ]

makeTermNot
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> TermLike variable
-- TODO: maybe other simplifications like
-- not ceil = floor not
-- not forall = exists not
makeTermNot term
  | isBottom term = mkTop    (termLikeSort term)
  | isTop term    = mkBottom (termLikeSort term)
  | otherwise = mkNot term
