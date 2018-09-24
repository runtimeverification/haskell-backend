{-|
Module      : Kore.Simplification.Implies
Description : Tools for Implies pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Implies
    (simplify
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkImplies )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeImpliesPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern), substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), isBottom, isTop, toMLPattern, top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, fmapFlattenWithPairs, isFalse, isTrue,
                 make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import qualified Kore.Step.Simplification.Not as Not
                 ( makeEvaluate, simplifyEvaluated )

{-|'simplify' simplifies an 'Implies' pattern with 'OrOfExpandedPattern'
children.

Right now this uses the following simplifications:

* a -> (b or c) = (a -> b) or (a -> c)
* bottom -> b = top
* top -> b = b
* a -> top = top
* a -> bottom = not a

and it has a special case for children with top terms.
-}
simplify
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => Implies level (OrOfExpandedPattern level Variable)
    ->  ( OrOfExpandedPattern level Variable
        , SimplificationProof level
        )
simplify
    Implies
        { impliesFirst = first
        , impliesSecond = second
        }
  =
    simplifyEvaluatedImplies first second

-- TODO: Maybe transform this to (not a) \/ b
simplifyEvaluatedImplies
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => OrOfExpandedPattern level Variable
    -> OrOfExpandedPattern level Variable
    -> (OrOfExpandedPattern level Variable, SimplificationProof level)
simplifyEvaluatedImplies first second
  | OrOfExpandedPattern.isTrue first =
    (second, SimplificationProof)
  | OrOfExpandedPattern.isFalse first =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isTrue second =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    Not.simplifyEvaluated first
  | otherwise =
    let
        (result, _proofs) =
            OrOfExpandedPattern.fmapFlattenWithPairs
                (simplifyEvaluateHalfImplies first)
                second
    in
        ( result , SimplificationProof )

simplifyEvaluateHalfImplies
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => OrOfExpandedPattern level Variable
    -> ExpandedPattern level Variable
    -> (OrOfExpandedPattern level Variable, SimplificationProof level)
simplifyEvaluateHalfImplies first second
  | OrOfExpandedPattern.isTrue first =
    (OrOfExpandedPattern.make [second], SimplificationProof)
  | OrOfExpandedPattern.isFalse first =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isTop second =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom second =
    Not.simplifyEvaluated first
  | otherwise =
    -- TODO: Also merge predicate-only patterns for 'Or'
    case OrOfExpandedPattern.extractPatterns first of
        [firstP] -> makeEvaluateImplies firstP second
        _ ->
            makeEvaluateImplies
                (OrOfExpandedPattern.toExpandedPattern first)
                second

makeEvaluateImplies
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => ExpandedPattern level Variable
    -> ExpandedPattern level Variable
    -> (OrOfExpandedPattern level Variable, SimplificationProof level)
makeEvaluateImplies
    first second
  | ExpandedPattern.isTop first =
    (OrOfExpandedPattern.make [second], SimplificationProof)
  | ExpandedPattern.isBottom first =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isTop second =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom second =
    Not.makeEvaluate first
  | otherwise =
    makeEvaluateImpliesNonBool first second

makeEvaluateImpliesNonBool
    ::  ( MetaOrObject level
        , Given (SortTools level)
        )
    => ExpandedPattern level Variable
    -> ExpandedPattern level Variable
    -> (OrOfExpandedPattern level Variable, SimplificationProof level)
makeEvaluateImpliesNonBool
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
                fst $ makeImpliesPredicate
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
makeEvaluateImpliesNonBool patt1 patt2 =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkImplies
                (ExpandedPattern.toMLPattern patt1)
                (ExpandedPattern.toMLPattern patt2)
            , predicate = makeTruePredicate
            , substitution = []
            }
        ]
    , SimplificationProof
    )
