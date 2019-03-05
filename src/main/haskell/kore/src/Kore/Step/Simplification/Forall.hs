{-|
Module      : Kore.Step.Simplification.Forall
Description : Tools for Forall pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Forall
    ( simplify
    , makeEvaluate
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( fmapWithPairs, isFalse, isTrue )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

-- TODO: Move Forall up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies an 'Forall' pattern with an 'OrOfExpandedPattern'
child.

Right now this has special cases only for top and bottom children.

Note that while forall x . phi(x) and [x=alpha] can be simplified
(it's bottom if x's sort is multivalued and alpha is not the 'x' pattern or
the identity function applied to the pattern x, or phi(alpha) otherwise),
we only expect forall usage for symbolic variables, so we won't attempt to
simplify it this way.

For this reason, we don't even try to see if the variable actually occurs in
the pattern except for the top/bottom cases.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Forall level variable (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Forall { forallVariable = variable, forallChild = child }
  =
    simplifyEvaluated variable child

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Forall level) (Valid level) (OrOfExpandedPattern level variable)

instead of a 'variable level' and an 'OrOfExpandedPattern' argument. The type of
'makeEvaluate' may be changed analogously. The 'Valid' annotation will
eventually cache information besides the pattern sort, which will make it even
more useful to carry around.

-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => variable level
    -> OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated variable simplified
  | OrOfExpandedPattern.isTrue simplified = (simplified, SimplificationProof)
  | OrOfExpandedPattern.isFalse simplified = (simplified, SimplificationProof)
  | otherwise =
    let
        (patt, _proofs) =
            OrOfExpandedPattern.fmapWithPairs (makeEvaluate variable) simplified
      in
        ( patt
        , SimplificationProof
        )

{-| evaluates an 'Forall' given its two 'ExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => variable level
    -> ExpandedPattern level variable
    -> (ExpandedPattern level variable, SimplificationProof level)
makeEvaluate variable patt
  | ExpandedPattern.isTop patt =
    (ExpandedPattern.top, SimplificationProof)
  | ExpandedPattern.isBottom patt =
    ( ExpandedPattern.bottom
    , SimplificationProof
    )
  | otherwise =
    ( Predicated
        { term = mkForall
            variable
            (ExpandedPattern.toMLPattern patt)
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    , SimplificationProof
    )
