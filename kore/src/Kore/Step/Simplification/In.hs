{-|
Module      : Kore.Step.Simplification.In
Description : Tools for In pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.In
    ( simplify
    ) where

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.Predicate as Predicate
                 ( topTODO )
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeInPredicate )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluate, simplifyEvaluated )
import           Kore.Step.Simplification.Data
import           Kore.Unparser
import           Kore.Variables.Fresh

{-|'simplify' simplifies an 'In' pattern with 'OrPattern'
children.

Right now this uses the following simplifications:

* bottom in a = bottom
* a in bottom = bottom
* top in a = ceil(a)
* a in top = ceil(a)

TODO(virgil): It does not have yet a special case for children with top terms.
-}
simplify
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => In Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify In { inContainedChild = first, inContainingChild = second } =
    simplifyEvaluatedIn first second

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make
'simplifyEvaluatedIn' take an argument of type

> CofreeF (In Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluateIn' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluatedIn
    :: forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => OrPattern variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluatedIn first second
  | OrPattern.isFalse first  = return OrPattern.bottom
  | OrPattern.isFalse second = return OrPattern.bottom

  | OrPattern.isTrue first = Ceil.simplifyEvaluated Predicate.topTODO second
  | OrPattern.isTrue second = Ceil.simplifyEvaluated Predicate.topTODO first

  | otherwise =
    OrPattern.flatten <$> sequence (makeEvaluateIn <$> first <*> second)

makeEvaluateIn
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => Pattern variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluateIn first second
  | Pattern.isTop first = Ceil.makeEvaluate Predicate.topTODO second
  | Pattern.isTop second = Ceil.makeEvaluate Predicate.topTODO first
  | Pattern.isBottom first || Pattern.isBottom second = return OrPattern.bottom
  | otherwise = return $ makeEvaluateNonBoolIn first second

makeEvaluateNonBoolIn
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern variable
    -> Pattern variable
    -> OrPattern variable
makeEvaluateNonBoolIn patt1 patt2 =
    OrPattern.fromPattern Conditional
        { term = mkTop_
        , predicate =
            makeInPredicate
                -- TODO: Wrap in 'contained' and 'container'.
                (Pattern.toTermLike patt1)
                (Pattern.toTermLike patt2)
        , substitution = mempty
        }
