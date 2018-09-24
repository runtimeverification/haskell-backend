{-|
Module      : Kore.Simplification.In
Description : Tools for In pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.In
    (simplify
    ) where

import Data.Reflection
       ( give )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
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
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, simplifyEvaluated )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

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
        )
    => MetadataTools level StepperAttributes
    -> In level (OrOfExpandedPattern level Variable)
    ->  ( OrOfExpandedPattern level Variable
        , SimplificationProof level
        )
simplify
    tools
    In
        { inContainedChild = first
        , inContainingChild = second
        }
  =
    simplifyEvaluatedIn tools first second

simplifyEvaluatedIn
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level Variable
    -> OrOfExpandedPattern level Variable
    -> (OrOfExpandedPattern level Variable, SimplificationProof level)
simplifyEvaluatedIn tools first second
  | OrOfExpandedPattern.isFalse first =
    (OrOfExpandedPattern.make [], SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    (OrOfExpandedPattern.make [], SimplificationProof)

  | OrOfExpandedPattern.isTrue first =
    Ceil.simplifyEvaluated tools second
  | OrOfExpandedPattern.isTrue second =
    Ceil.simplifyEvaluated tools first

  | otherwise =
    -- TODO: It's not obvious at all when filtering occurs and when it doesn't.
    ( OrOfExpandedPattern.flatten
        -- TODO: Remove fst.
        (fst <$> OrOfExpandedPattern.crossProductGeneric
            (makeEvaluateIn tools) first second
        )
    , SimplificationProof
    )

makeEvaluateIn
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level Variable
    -> ExpandedPattern level Variable
    -> (OrOfExpandedPattern level Variable, SimplificationProof level)
makeEvaluateIn tools first second
  | ExpandedPattern.isTop first =
    Ceil.makeEvaluate tools second
  | ExpandedPattern.isTop second =
    Ceil.makeEvaluate tools first
  | ExpandedPattern.isBottom first || ExpandedPattern.isBottom second =
    (OrOfExpandedPattern.make [], SimplificationProof)
  | otherwise = makeEvaluateNonBoolIn tools first second

makeEvaluateNonBoolIn
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level Variable
    -> ExpandedPattern level Variable
    -> (OrOfExpandedPattern level Variable, SimplificationProof level)
makeEvaluateNonBoolIn tools patt1 patt2 =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkTop
            , predicate = give sortTools $ makeInPredicate
                -- TODO: Wrap in 'contained' and 'container'.
                (ExpandedPattern.toMLPattern patt1)
                (ExpandedPattern.toMLPattern patt2)
            , substitution = []
            }
        ]
    , SimplificationProof
    )
  where
    sortTools = MetadataTools.sortTools tools
