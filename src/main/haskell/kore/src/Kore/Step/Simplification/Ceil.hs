{-|
Module      : Kore.Simplification.Ceil
Description : Tools for Ceil pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Ceil
    ( simplify
    , makeEvaluateCeil
    , simplifyEvaluatedCeil
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Ceil (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeCeilPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, isBottom, isTop, top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( fmapFlattenWithPairs, make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| 'simplify' simplifies a 'Ceil' of 'OrOfExpandedPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates

However, we don't take into account things like ceil(functional) = top.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => Ceil level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Ceil { ceilChild = child }
  =
    simplifyEvaluatedCeil child

{-| 'simplifyEvaluatedCeil' evaluates a ceil given its child, see 'simplify'
for details.
-}
simplifyEvaluatedCeil
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluatedCeil child =
    ( evaluated, SimplificationProof )
  where
    (evaluated, _proofs) =
        OrOfExpandedPattern.fmapFlattenWithPairs makeEvaluateCeil child

{-| 'simplifyEvaluatedCeil' evaluates a ceil given its child as
an ExpandedPattern, see 'simplify' for details.
-}
makeEvaluateCeil
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateCeil child
  | ExpandedPattern.isTop child =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom child =
    (OrOfExpandedPattern.make [ExpandedPattern.bottom], SimplificationProof)
  | otherwise =
    makeEvaluateNonBoolCeil child

makeEvaluateNonBoolCeil
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolCeil
    patt@ExpandedPattern { term = Top_ _ }
  =
    ( OrOfExpandedPattern.make [patt]
    , SimplificationProof
    )
-- TODO: Also evaluate functional patterns to true, and maybe other cases also
makeEvaluateNonBoolCeil
    ExpandedPattern {term, predicate, substitution}
  =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkTop
            , predicate =
                case makeAndPredicate (makeCeilPredicate term) predicate of
                    (predicate', _proof) -> predicate'
            , substitution = substitution
            }
        ]
    , SimplificationProof
    )
