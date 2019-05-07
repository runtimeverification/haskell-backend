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

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
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
    => Rewrites Sort (OrPattern variable)
    -> OrPattern variable
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

> CofreeF (Or Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of
'makeEvaluateRewrites' may be changed analogously. The 'Attribute.Pattern'
annotation will eventually cache information besides the pattern sort, which
will make it even more useful to carry around.

-}
simplifyEvaluatedRewrites
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => OrPattern variable
    -> OrPattern variable
    -> OrPattern variable
simplifyEvaluatedRewrites first second =
    makeEvaluateRewrites
        (OrPattern.toPattern first)
        (OrPattern.toPattern second)

makeEvaluateRewrites
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern variable
    -> Pattern variable
    -> OrPattern variable
makeEvaluateRewrites first second =
    OrPattern.fromTermLike
    $ mkRewrites
        (Pattern.toMLPattern first)
        (Pattern.toMLPattern second)
