{-|
Module      : Kore.Step.Simplification.Not
Description : Tools for Not pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Not
    ( makeEvaluate
    , simplify
    , simplifyEvaluated
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Not (..), PureMLPattern, SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkBottom, mkNot, mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_, pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeNotPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..), substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( toMLPattern, top )
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
        , Given (SymbolOrAliasSorts level)
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
    simplifyEvaluated child

{-|'simplifyEvaluated' simplifies a 'Not' pattern given its
'OrOfExpandedPattern' child.

See 'simplify' for details.
-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated simplified
  | OrOfExpandedPattern.isFalse simplified =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  | OrOfExpandedPattern.isTrue simplified =
    (OrOfExpandedPattern.make [], SimplificationProof)
  | otherwise =
    case OrOfExpandedPattern.extractPatterns simplified of
        [patt] -> makeEvaluate patt
        _ ->
            ( makeFromSinglePurePattern
                (mkNot
                    (ExpandedPattern.toMLPattern
                        (OrOfExpandedPattern.toExpandedPattern simplified)
                    )
                )
            , SimplificationProof
            )

{-|'makeEvaluate' simplifies a 'Not' pattern given its 'ExpandedPattern'
child.

See 'simplify' for details.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluate
    Predicated {term, predicate, substitution}
  =
    ( OrOfExpandedPattern.make
        [ Predicated
            { term = makeTermNot term
            , predicate = makeTruePredicate
            , substitution = []
            }
        , Predicated
            -- TODO: Remove fst.
            { term = mkTop
            , predicate =
                makeNotPredicate
                    (makeAndPredicate
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
        , Given (SymbolOrAliasSorts level)
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
