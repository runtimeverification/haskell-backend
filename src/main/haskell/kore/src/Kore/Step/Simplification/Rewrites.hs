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
    ( simplify
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( toMLPattern )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

{-|'simplify' simplifies a 'Rewrites' pattern with an 'OrOfExpandedPattern'
child.

Right now this does not do any actual simplification.

TODO(virgil): Should I even bother to simplify Rewrites? Maybe to implies+next?
-}
simplify
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
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

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make
'simplifyEvaluatedRewrites' take an argument of type

> CofreeF (Or level) (Valid level) (OrOfExpandedPattern level variable)

instead of two 'OrOfExpandedPattern' arguments. The type of
'makeEvaluateRewrites' may be changed analogously. The 'Valid' annotation will
eventually cache information besides the pattern sort, which will make it even
more useful to carry around.

-}
simplifyEvaluatedRewrites
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => OrOfExpandedPattern Object variable
    -> OrOfExpandedPattern Object variable
    -> (OrOfExpandedPattern Object variable, SimplificationProof Object)
simplifyEvaluatedRewrites first second =
    makeEvaluateRewrites
        (OrOfExpandedPattern.toExpandedPattern first)
        (OrOfExpandedPattern.toExpandedPattern second)

makeEvaluateRewrites
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => ExpandedPattern Object variable
    -> ExpandedPattern Object variable
    -> (OrOfExpandedPattern Object variable, SimplificationProof Object)
makeEvaluateRewrites first second =
    ( MultiOr.make
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
