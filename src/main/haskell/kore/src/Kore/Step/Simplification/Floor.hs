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
                 ( SymbolOrAliasSorts )
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
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

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
        , Given (SymbolOrAliasSorts level)
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
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
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
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
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
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolFloor
    patt@ExpandedPattern { term = Top_ _ }
  =
    ( OrOfExpandedPattern.make [patt]
    , SimplificationProof
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
                    (predicate', _proof) -> predicate'
            , substitution = substitution
            }
        ]
    , SimplificationProof
    )
