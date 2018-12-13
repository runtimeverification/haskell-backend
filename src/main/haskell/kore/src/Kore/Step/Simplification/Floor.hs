{-|
Module      : Kore.Step.Simplification.Floor
Description : Tools for Floor pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Floor
    ( simplify
    , makeEvaluateFloor
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeFloorPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

{-| 'simplify' simplifies a 'Floor' of 'OrOfExpandedPattern'.

We also take into account that
* floor(top) = top
* floor(bottom) = bottom
* floor leaves predicates and substitutions unchanged
* floor transforms terms into predicates

However, we don't take into account things like
floor(a and b) = floor(a) and floor(b).
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Unparse (variable level)
        , Show (variable level)
        , Ord (variable level)
        )
    => Floor level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Floor { floorChild = child }
  =
    simplifyEvaluatedFloor child

simplifyEvaluatedFloor
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Unparse (variable level)
        )
    => OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluatedFloor child =
    case OrOfExpandedPattern.extractPatterns child of
        [childP] -> makeEvaluateFloor childP
        _ ->
            makeEvaluateFloor
                (OrOfExpandedPattern.toExpandedPattern child)

{-| 'makeEvaluateFloor' simplifies a 'Floor' of 'ExpandedPattern'.

See 'simplify' for details.
-}
makeEvaluateFloor
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateFloor child
  | ExpandedPattern.isTop child =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom child =
    (OrOfExpandedPattern.make [ExpandedPattern.bottom], SimplificationProof)
  | otherwise =
    makeEvaluateNonBoolFloor child

makeEvaluateNonBoolFloor
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolFloor
    patt@Predicated { term = Top_ _ }
  =
    ( OrOfExpandedPattern.make [patt]
    , SimplificationProof
    )
-- TODO(virgil): Also evaluate functional patterns to bottom for non-singleton
-- sorts, and maybe other cases also
makeEvaluateNonBoolFloor
    Predicated {term, predicate, substitution}
  =
    ( OrOfExpandedPattern.make
        [ Predicated
            { term = mkTop_
            , predicate = makeAndPredicate (makeFloorPredicate term) predicate
            , substitution = substitution
            }
        ]
    , SimplificationProof
    )
