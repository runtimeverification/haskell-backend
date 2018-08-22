{-|
Module      : Kore.Simplification.Iff
Description : Tools for Iff pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Iff
    (simplify
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Iff (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkIff )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeIffPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern), substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), isBottom, isTop, toMLPattern )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, isFalse, isTrue, make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.Simplification.Not
                 ( makeEvaluateNot, simplifyEvaluatedNot )

{-|'simplify' simplifies an 'Iff' pattern with 'OrOfExpandedPattern'
children.

Right now this has special cases only for top and bottom children
and for children with top terms.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => Iff level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Iff
        { iffFirst = first
        , iffSecond = second
        }
  =
    simplifyEvaluatedIff first second

simplifyEvaluatedIff
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluatedIff first second
  | OrOfExpandedPattern.isTrue first =
    (second, SimplificationProof)
  | OrOfExpandedPattern.isFalse first =
    simplifyEvaluatedNot second
  | OrOfExpandedPattern.isTrue second =
    (first, SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    simplifyEvaluatedNot first
  | otherwise =
    case ( firstPatterns, secondPatterns )
      of
        ([firstP], [secondP]) -> makeEvaluateIff firstP secondP
        _ ->
            makeEvaluateIff
                (OrOfExpandedPattern.toExpandedPattern first)
                (OrOfExpandedPattern.toExpandedPattern second)
  where
    firstPatterns = OrOfExpandedPattern.extractPatterns first
    secondPatterns = OrOfExpandedPattern.extractPatterns second

makeEvaluateIff
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateIff first second
  | ExpandedPattern.isTop first =
    (OrOfExpandedPattern.make [second], SimplificationProof)
  | ExpandedPattern.isBottom first =
    (fst $ makeEvaluateNot second, SimplificationProof)
  | ExpandedPattern.isTop second =
    (OrOfExpandedPattern.make [first], SimplificationProof)
  | ExpandedPattern.isBottom second =
    (fst $ makeEvaluateNot first, SimplificationProof)
  | otherwise =
    makeEvaluateNonBoolIff first second

makeEvaluateNonBoolIff
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolIff
    ExpandedPattern
        { term = t@(Top_ _)
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    ExpandedPattern
        { term = Top_ _
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = t
            , predicate =
                -- TODO: Remove fst
                fst $ makeIffPredicate
                    -- TODO: Remove fst
                    (fst $ makeAndPredicate
                        firstPredicate
                        (substitutionToPredicate firstSubstitution))
                    -- TODO: Remove fst
                    (fst $ makeAndPredicate
                        secondPredicate
                        (substitutionToPredicate secondSubstitution)
                    )
            , substitution = []
            }
        ]
    , SimplificationProof
    )
makeEvaluateNonBoolIff patt1 patt2 =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkIff
                (ExpandedPattern.toMLPattern patt1)
                (ExpandedPattern.toMLPattern patt2)
            , predicate = makeTruePredicate
            , substitution = []
            }
        ]
    , SimplificationProof
    )
