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

import qualified Data.Functor.Foldable as Recursive

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeNotPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( toMLPattern, top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern, makeFromSinglePurePattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, isFalse, isTrue, make, toExpandedPattern )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

{-|'simplify' simplifies a 'Not' pattern with an 'OrOfExpandedPattern'
child.

Right now this uses the following:

* not top = bottom
* not bottom = top

-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Not level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Not { notChild = child }
  =
    simplifyEvaluated child

{-|'simplifyEvaluated' simplifies a 'Not' pattern given its
'OrOfExpandedPattern' child.

See 'simplify' for details.
-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated simplified
  | OrOfExpandedPattern.isFalse simplified =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isTrue simplified =
    (OrOfExpandedPattern.make [], SimplificationProof)
  | otherwise =
    case OrOfExpandedPattern.extractPatterns simplified of
        [patt] -> makeEvaluate patt
        _ ->
            ( makeFromSinglePurePattern
                (mkNot
                    (ExpandedPattern.toMLPattern
                        (OrOfExpandedPattern.toExpandedPattern simplified)
                    )
                )
            , SimplificationProof
            )

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
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate
    Predicated {term, predicate, substitution}
  =
    ( OrOfExpandedPattern.make
        [ Predicated
            { term = makeTermNot term
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        , Predicated
            { term = mkTop_
            , predicate =
                makeNotPredicate
                    (makeAndPredicate
                        predicate
                        (substitutionToPredicate substitution)
                    )
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )

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
