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

import           Kore.AST.Valid
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Syntax.Rewrites
import           Kore.Unparser

{- | Simplify a 'Rewrites' pattern with a 'OrPattern' child.

Right now this does not do any actual simplification.

TODO(virgil): Should I even bother to simplify Rewrites? Maybe to implies+next?
-}
simplify
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Rewrites Sort (OrPattern Object variable)
    ->  ( OrPattern Object variable
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

> CofreeF (Or Sort) (Valid Object) (OrPattern Object variable)

instead of two 'OrPattern' arguments. The type of
'makeEvaluateRewrites' may be changed analogously. The 'Valid' annotation will
eventually cache information besides the pattern sort, which will make it even
more useful to carry around.

-}
simplifyEvaluatedRewrites
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => OrPattern Object variable
    -> OrPattern Object variable
    -> (OrPattern Object variable, SimplificationProof Object)
simplifyEvaluatedRewrites first second =
    makeEvaluateRewrites
        (OrPattern.toExpandedPattern first)
        (OrPattern.toExpandedPattern second)

makeEvaluateRewrites
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern Object variable
    -> Pattern Object variable
    -> (OrPattern Object variable, SimplificationProof Object)
makeEvaluateRewrites first second =
    ( OrPattern.fromPattern
        $ Pattern.fromTermLike
        $ mkRewrites
            (Pattern.toMLPattern first)
            (Pattern.toMLPattern second)
    , SimplificationProof
    )
