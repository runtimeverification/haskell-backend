{-|
Module      : Kore.Simplification.Not
Description : Tools for Not pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Not
    ( makeEvaluateNot
    , simplify
    , simplifyEvaluatedNot
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Not (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkNot, mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_, pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeNotPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern), substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), toMLPattern, top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern, makeFromSinglePurePattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, isFalse, isTrue, make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-|'simplify' simplifies a 'Not' pattern with an 'OrOfExpandedPattern'
child.

Right now this uses the following:

* not top = bottom
* not bottom = top

-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => Not level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Not { notChild = child }
  =
    simplifyEvaluatedNot child

{-|'makeEvaluateNot' simplifies a 'Not' pattern given its 'OrOfExpandedPattern'
child.

See 'simplify' for details.
-}
simplifyEvaluatedNot
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluatedNot simplified
  | OrOfExpandedPattern.isFalse simplified =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isTrue simplified =
    (OrOfExpandedPattern.make [], SimplificationProof)
  | otherwise =
    case OrOfExpandedPattern.extractPatterns simplified of
        [patt] -> makeEvaluateNot patt
        _ ->
            ( makeFromSinglePurePattern
                (mkNot
                    (ExpandedPattern.toMLPattern
                        (OrOfExpandedPattern.toExpandedPattern simplified)
                    )
                )
            , SimplificationProof
            )

{-|'makeEvaluateNot' simplifies a 'Not' pattern given its 'ExpandedPattern'
child.

See 'simplify' for details.
-}
makeEvaluateNot
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateNot
    ExpandedPattern {term, predicate, substitution}
  =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = makeTermNot term
            , predicate = makeTruePredicate
            , substitution = []
            }
        , ExpandedPattern
            -- TODO: Remove fst.
            { term = mkTop
            , predicate =
                fst $ makeNotPredicate
                    (fst $ makeAndPredicate
                        predicate
                        (substitutionToPredicate substitution)
                    )
            , substitution = []
            }
        ]
    , SimplificationProof
    )

makeTermNot
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => PureMLPattern level variable
    -> PureMLPattern level variable
makeTermNot (Bottom_ _) = mkTop
makeTermNot (Top_ _) = mkBottom
-- TODO: maybe other simplifications like
-- not ceil = floor not
-- not forall = exists not
makeTermNot term = mkNot term
