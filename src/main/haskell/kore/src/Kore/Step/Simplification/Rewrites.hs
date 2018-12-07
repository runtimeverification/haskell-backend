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
                 ( Rewrites (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkRewrites )
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( toMLPattern )
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
    ::  ( SortedVariable variable
        , Given (SymbolOrAliasSorts Object)
        , Show (variable Object)
        , Ord (variable Object)
        )
    => Rewrites Object (OrOfExpandedPattern Object variable)
    ->  ( OrOfExpandedPattern Object variable
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
    ::  ( SortedVariable variable
        , Given (SymbolOrAliasSorts Object)
        , Show (variable Object)
        , Ord (variable Object)
        )
    => OrOfExpandedPattern Object variable
    -> OrOfExpandedPattern Object variable
    -> (OrOfExpandedPattern Object variable, SimplificationProof Object)
simplifyEvaluatedRewrites first second =
    makeEvaluateRewrites
        (OrOfExpandedPattern.toExpandedPattern first)
        (OrOfExpandedPattern.toExpandedPattern second)

makeEvaluateRewrites
    ::  ( SortedVariable variable
        , Given (SymbolOrAliasSorts Object)
        , Show (variable Object)
        , Ord (variable Object)
        )
    => ExpandedPattern Object variable
    -> ExpandedPattern Object variable
    -> (OrOfExpandedPattern Object variable, SimplificationProof Object)
makeEvaluateRewrites first second =
    ( OrOfExpandedPattern.make
        [ Predicated
            { term = mkRewrites
                (ExpandedPattern.toMLPattern first)
                (ExpandedPattern.toMLPattern second)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
