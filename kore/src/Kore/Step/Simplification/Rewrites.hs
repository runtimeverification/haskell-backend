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

import           Kore.AST.Common
                 ( Rewrites (..) )
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import qualified Kore.Step.Or as Or
import           Kore.Step.Pattern
import           Kore.Step.Pattern as Pattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

{-|'simplify' simplifies a 'Rewrites' pattern with an 'OrOfExpandedPattern'
child.

Right now this does not do any actual simplification.

TODO(virgil): Should I even bother to simplify Rewrites? Maybe to implies+next?
-}
simplify
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Rewrites Object (Or.Pattern Object variable)
    ->  ( Or.Pattern Object variable
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

> CofreeF (Or Object) (Valid Object) (Or.Pattern Object variable)

instead of two 'Or.Pattern' arguments. The type of
'makeEvaluateRewrites' may be changed analogously. The 'Valid' annotation will
eventually cache information besides the pattern sort, which will make it even
more useful to carry around.

-}
simplifyEvaluatedRewrites
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Or.Pattern Object variable
    -> Or.Pattern Object variable
    -> (Or.Pattern Object variable, SimplificationProof Object)
simplifyEvaluatedRewrites first second =
    makeEvaluateRewrites
        (Or.toExpandedPattern first)
        (Or.toExpandedPattern second)

makeEvaluateRewrites
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable
    -> Pattern Object variable
    -> (Or.Pattern Object variable, SimplificationProof Object)
makeEvaluateRewrites first second =
    ( MultiOr.make
        [ Conditional
            { term = mkRewrites
                (Pattern.toMLPattern first)
                (Pattern.toMLPattern second)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
