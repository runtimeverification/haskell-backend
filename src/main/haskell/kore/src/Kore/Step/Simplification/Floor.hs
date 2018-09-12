{-|
Module      : Kore.Simplification.Floor
Description : Tools for Floor pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Floor
    ( simplify
    , makeEvaluateFloor
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Floor (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeFloorPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, isBottom, isTop, top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, toExpandedPattern )

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
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => Floor level (OrOfExpandedPattern level domain variable)
    ->  ( OrOfExpandedPattern level domain variable
        , ()
        )
simplify
    Floor { floorChild = child }
  =
    simplifyEvaluatedFloor child

simplifyEvaluatedFloor
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level domain variable
    -> (OrOfExpandedPattern level domain variable, ())
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
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level domain variable
    -> (OrOfExpandedPattern level domain variable, ())
makeEvaluateFloor child
  | ExpandedPattern.isTop child =
    (OrOfExpandedPattern.make [ExpandedPattern.top], ())
  | ExpandedPattern.isBottom child =
    (OrOfExpandedPattern.make [ExpandedPattern.bottom], ())
  | otherwise =
    makeEvaluateNonBoolFloor child

makeEvaluateNonBoolFloor
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level domain variable
    -> (OrOfExpandedPattern level domain variable, ())
makeEvaluateNonBoolFloor
    patt@ExpandedPattern { term = Top_ _ }
  =
    ( OrOfExpandedPattern.make [patt]
    , ()
    )
-- TODO(virgil): Also evaluate functional patterns to bottom for non-singleton
-- sorts, and maybe other cases also
makeEvaluateNonBoolFloor
    ExpandedPattern {term, predicate, substitution}
  =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkTop
            , predicate =
                case makeAndPredicate (makeFloorPredicate term) predicate of
                    (predicate', _) -> predicate'
            , substitution = substitution
            }
        ]
    , ()
    )
