{-|
Module      : Kore.Step.Simplification.Floor
Description : Tools for Floor pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Floor
    ( simplify
    , makeEvaluateFloor
    ) where

import           Kore.AST.Common
                 ( Floor (..) )
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeFloorPredicate )
import qualified Kore.Step.Or as Or
import           Kore.Step.Pattern as Pattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( extractPatterns, make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

{-| 'simplify' simplifies a 'Floor' of 'Or.Pattern'.

We also take into account that
* floor(top) = top
* floor(bottom) = bottom
* floor leaves predicates and substitutions unchanged
* floor transforms terms into predicates

However, we don't take into account things like
floor(a and b) = floor(a) and floor(b).
-}
simplify
    ::  ( SortedVariable variable
        , Unparse (variable Object)
        , Show (variable Object)
        , Ord (variable Object)
        )
    => Floor Object (Or.Pattern Object variable)
    ->  ( Or.Pattern Object variable
        , SimplificationProof Object
        )
simplify
    Floor { floorChild = child }
  =
    simplifyEvaluatedFloor child

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Floor Object) (Valid Object) (Or.Pattern Object variable)

instead of an 'Or.Pattern' argument. The type of 'makeEvaluateFloor'
may be changed analogously. The 'Valid' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluatedFloor
    ::  ( SortedVariable variable
        , Show (variable Object)
        , Ord (variable Object)
        , Unparse (variable Object)
        )
    => Or.Pattern Object variable
    -> (Or.Pattern Object variable, SimplificationProof Object)
simplifyEvaluatedFloor child =
    case MultiOr.extractPatterns child of
        [childP] -> makeEvaluateFloor childP
        _ ->
            makeEvaluateFloor
                (Or.toExpandedPattern child)

{-| 'makeEvaluateFloor' simplifies a 'Floor' of 'Pattern'.

See 'simplify' for details.
-}
makeEvaluateFloor
    ::  ( SortedVariable variable
        , Show (variable Object)
        , Ord (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable
    -> (Or.Pattern Object variable, SimplificationProof Object)
makeEvaluateFloor child
  | Pattern.isTop child =
    (MultiOr.make [Pattern.top], SimplificationProof)
  | Pattern.isBottom child =
    (MultiOr.make [Pattern.bottom], SimplificationProof)
  | otherwise =
    makeEvaluateNonBoolFloor child

makeEvaluateNonBoolFloor
    ::  ( SortedVariable variable
        , Show (variable Object)
        , Ord (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable
    -> (Or.Pattern Object variable, SimplificationProof Object)
makeEvaluateNonBoolFloor
    patt@Conditional { term = Top_ _ }
  =
    ( MultiOr.make [patt]
    , SimplificationProof
    )
-- TODO(virgil): Also evaluate functional patterns to bottom for non-singleton
-- sorts, and maybe other cases also
makeEvaluateNonBoolFloor
    Conditional {term, predicate, substitution}
  =
    ( MultiOr.make
        [ Conditional
            { term = mkTop_
            , predicate = makeAndPredicate (makeFloorPredicate term) predicate
            , substitution = substitution
            }
        ]
    , SimplificationProof
    )
