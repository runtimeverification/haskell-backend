{-|
Module      : Kore.Simplification.Rewrites
Description : Tools for Rewrites pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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
                 ( Rewrites (..), SortedVariable )
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

{-|'simplify' simplifies a 'Rewrites' pattern with an 'OrOfExpandedPattern'
child.

Right now this does not do any actual simplification.

TODO(virgil): Should I even bother to simplify Rewrites? Maybe to implies+next?
-}
simplify
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Given (SortTools Object)
        , Show (variable Object)
        , Ord (variable Object)
        )
    => Rewrites Object (OrOfExpandedPattern Object domain variable)
    ->  ( OrOfExpandedPattern Object domain variable
        , ()
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
        , SortedVariable variable
        , Given (SortTools Object)
        , Show (variable Object)
        , Ord (variable Object)
        )
    => OrOfExpandedPattern Object domain variable
    -> OrOfExpandedPattern Object domain variable
    -> (OrOfExpandedPattern Object domain variable, ())
simplifyEvaluatedRewrites first second =
    makeEvaluateRewrites
        (OrOfExpandedPattern.toExpandedPattern first)
        (OrOfExpandedPattern.toExpandedPattern second)

makeEvaluateRewrites
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Given (SortTools Object)
        , Show (variable Object)
        , Ord (variable Object)
        )
    => ExpandedPattern Object domain variable
    -> ExpandedPattern Object domain variable
    -> (OrOfExpandedPattern Object domain variable, ())
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
    , ()
    )
