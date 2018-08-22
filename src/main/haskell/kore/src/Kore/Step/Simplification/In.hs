{-|
Module      : Kore.Simplification.In
Description : Tools for In pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.In
    (simplify
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( In (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeInPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), isBottom, isTop, toMLPattern )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( crossProductGeneric, flatten, isFalse, isTrue, make )
import           Kore.Step.Simplification.Ceil
                 ( makeEvaluateCeil, simplifyEvaluatedCeil )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-|'simplify' simplifies an 'In' pattern with 'OrOfExpandedPattern'
children.

Right now this uses the following simplifications:

* bottom in a = bottom
* a in bottom = bottom
* top in a = ceil(a)
* a in top = ceil(a)

TODO(virgil): It does not have yet a special case for children with top terms.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => In level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    In
        { inContainedChild = first
        , inContainingChild = second
        }
  =
    simplifyEvaluatedIn first second

simplifyEvaluatedIn
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluatedIn first second
  | OrOfExpandedPattern.isFalse first =
    (OrOfExpandedPattern.make [], SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    (OrOfExpandedPattern.make [], SimplificationProof)

  | OrOfExpandedPattern.isTrue first =
    simplifyEvaluatedCeil second
  | OrOfExpandedPattern.isTrue second =
    simplifyEvaluatedCeil first

  | otherwise =
    -- TODO: It's not obvious at all when filtering occurs and when it doesn't.
    ( OrOfExpandedPattern.flatten
        -- TODO: Remove fst.
        (fst <$> OrOfExpandedPattern.crossProductGeneric
            makeEvaluateIn first second
        )
    , SimplificationProof
    )

makeEvaluateIn
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateIn first second
  | ExpandedPattern.isTop first =
    makeEvaluateCeil second
  | ExpandedPattern.isTop second =
    makeEvaluateCeil second
  | ExpandedPattern.isBottom first || ExpandedPattern.isBottom second =
    (OrOfExpandedPattern.make [], SimplificationProof)
  | otherwise = makeEvaluateNonBoolIn first second

makeEvaluateNonBoolIn
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolIn patt1 patt2 =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkTop
            , predicate = makeInPredicate
                -- TODO: Wrap in 'contained' and 'container'.
                (ExpandedPattern.toMLPattern patt1)
                (ExpandedPattern.toMLPattern patt2)
            , substitution = []
            }
        ]
    , SimplificationProof
    )
