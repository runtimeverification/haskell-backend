{-|
Module      : Kore.Step.Simplification.Rewrites
Description : Tools for Rewrites pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Rewrites
    (simplify
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkRewrites )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), toMLPattern )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-|'simplify' simplifies a 'Rewrites' pattern with an 'OrOfExpandedPattern'
child.

Right now this does not do any actual simplification.

TODO(virgil): Should I even bother to simplify Rewrites? Maybe to implies+next?
-}
simplify
    ::  ( MetaOrObject Object
        , Given (SortTools Object)
        )
    => Rewrites Object (OrOfExpandedPattern Object Variable)
    ->  ( OrOfExpandedPattern Object Variable
        , SimplificationProof Object
        )
simplify
    Rewrites
        { rewritesFirst = first
        , rewritesSecond = second
        }
  =
    simplifyEvaluatedRewrites first second

simplifyEvaluatedRewrites
    ::  ( MetaOrObject Object
        , Given (SortTools Object)
        )
    => OrOfExpandedPattern Object Variable
    -> OrOfExpandedPattern Object Variable
    -> (OrOfExpandedPattern Object Variable, SimplificationProof Object)
simplifyEvaluatedRewrites first second =
    makeEvaluateRewrites
        (OrOfExpandedPattern.toExpandedPattern first)
        (OrOfExpandedPattern.toExpandedPattern second)

makeEvaluateRewrites
    ::  ( MetaOrObject Object
        , Given (SortTools Object)
        )
    => ExpandedPattern Object Variable
    -> ExpandedPattern Object Variable
    -> (OrOfExpandedPattern Object Variable, SimplificationProof Object)
makeEvaluateRewrites first second =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkRewrites
                (ExpandedPattern.toMLPattern first)
                (ExpandedPattern.toMLPattern second)
            , predicate = makeTruePredicate
            , substitution = []
            }
        ]
    , SimplificationProof
    )
