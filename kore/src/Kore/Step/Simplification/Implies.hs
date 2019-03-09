{-|
Module      : Kore.Step.Simplification.Implies
Description : Tools for Implies pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Implies
    ( simplify
    , simplifyEvaluated
    ) where

import qualified Data.Functor.Foldable as Recursive

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeImpliesPredicate, makeTruePredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), substitutionToPredicate )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( extractPatterns, fmapFlattenWithPairs, make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import qualified Kore.Step.Simplification.Not as Not
                 ( makeEvaluate, simplifyEvaluated )
import           Kore.Unparser

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
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Implies level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Implies
        { impliesFirst = first
        , impliesSecond = second
        }
  =
    simplifyEvaluated first second

{-| simplifies an Implies given its two 'OrOfExpandedPattern' children.

See 'simplify' for details.
-}
-- TODO: Maybe transform this to (not a) \/ b
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Implies level) (Valid level) (OrOfExpandedPattern level variable)

instead of two 'OrOfExpandedPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated first second
  | OrOfExpandedPattern.isTrue first =
    (second, SimplificationProof)
  | OrOfExpandedPattern.isFalse first =
    (MultiOr.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isTrue second =
    (MultiOr.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    Not.simplifyEvaluated first
  | otherwise =
    let
        (result, _proofs) =
            MultiOr.fmapFlattenWithPairs
                (simplifyEvaluateHalfImplies first)
                second
    in
        ( result , SimplificationProof )

simplifyEvaluateHalfImplies
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => OrOfExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluateHalfImplies first second
  | OrOfExpandedPattern.isTrue first =
    (MultiOr.make [second], SimplificationProof)
  | OrOfExpandedPattern.isFalse first =
    (MultiOr.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isTop second =
    (MultiOr.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom second =
    Not.simplifyEvaluated first
  | otherwise =
    -- TODO: Also merge predicate-only patterns for 'Or'
    case MultiOr.extractPatterns first of
        [firstP] -> makeEvaluateImplies firstP second
        _ ->
            makeEvaluateImplies
                (OrOfExpandedPattern.toExpandedPattern first)
                second

makeEvaluateImplies
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateImplies
    first second
  | ExpandedPattern.isTop first =
    (MultiOr.make [second], SimplificationProof)
  | ExpandedPattern.isBottom first =
    (MultiOr.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isTop second =
    (MultiOr.make [ExpandedPattern.top], SimplificationProof)
  | ExpandedPattern.isBottom second =
    Not.makeEvaluate first
  | otherwise =
    makeEvaluateImpliesNonBool first second

makeEvaluateImpliesNonBool
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateImpliesNonBool
    pattern1@Predicated
        { term = firstTerm
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    pattern2@Predicated
        { term = secondTerm
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  | (Recursive.project -> _ :< TopPattern _) <- firstTerm
  , (Recursive.project -> _ :< TopPattern _) <- secondTerm
  =
    ( MultiOr.make
        [ Predicated
            { term = firstTerm
            , predicate =
                makeImpliesPredicate
                    (makeAndPredicate
                        firstPredicate
                        (substitutionToPredicate firstSubstitution))
                    (makeAndPredicate
                        secondPredicate
                        (substitutionToPredicate secondSubstitution)
                    )
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
  | otherwise =
    ( MultiOr.make
        [ Predicated
            { term =
                mkImplies
                    (ExpandedPattern.toMLPattern pattern1)
                    (ExpandedPattern.toMLPattern pattern2)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
