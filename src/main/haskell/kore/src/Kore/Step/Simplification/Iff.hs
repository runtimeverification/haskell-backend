{-|
Module      : Kore.Step.Simplification.Iff
Description : Tools for Iff pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Iff
    ( makeEvaluate
    , simplify
    , simplifyEvaluated
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
                 ( SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeIffPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, isFalse, isTrue, make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import qualified Kore.Step.Simplification.Not as Not
                 ( makeEvaluate, simplifyEvaluated )

{-|'simplify' simplifies an 'Iff' pattern with 'OrOfExpandedPattern'
children.

Right now this has special cases only for top and bottom children
and for children with top terms.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
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
    simplifyEvaluated first second

{-| evaluates an 'Iff' given its two 'OrOfExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated first second
  | OrOfExpandedPattern.isTrue first =
    (second, SimplificationProof)
  | OrOfExpandedPattern.isFalse first =
    Not.simplifyEvaluated second
  | OrOfExpandedPattern.isTrue second =
    (first, SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    Not.simplifyEvaluated first
  | otherwise =
    case ( firstPatterns, secondPatterns )
      of
        ([firstP], [secondP]) -> makeEvaluate firstP secondP
        _ ->
            makeEvaluate
                (OrOfExpandedPattern.toExpandedPattern first)
                (OrOfExpandedPattern.toExpandedPattern second)
  where
    firstPatterns = OrOfExpandedPattern.extractPatterns first
    secondPatterns = OrOfExpandedPattern.extractPatterns second

{-| evaluates an 'Iff' given its two 'ExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate first second
  | ExpandedPattern.isTop first =
    (OrOfExpandedPattern.make [second], SimplificationProof)
  | ExpandedPattern.isBottom first =
    (fst $ Not.makeEvaluate second, SimplificationProof)
  | ExpandedPattern.isTop second =
    (OrOfExpandedPattern.make [first], SimplificationProof)
  | ExpandedPattern.isBottom second =
    (fst $ Not.makeEvaluate first, SimplificationProof)
  | otherwise =
    makeEvaluateNonBoolIff first second

makeEvaluateNonBoolIff
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBoolIff
    Predicated
        { term = t@(Top_ _)
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    Predicated
        { term = Top_ _
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  =
    ( OrOfExpandedPattern.make
        [ Predicated
            { term = t
            , predicate =
                makeIffPredicate
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
makeEvaluateNonBoolIff patt1 patt2 =
    ( OrOfExpandedPattern.make
        [ Predicated
            { term = mkIff
                (ExpandedPattern.toMLPattern patt1)
                (ExpandedPattern.toMLPattern patt2)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
