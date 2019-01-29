{-|
Module      : Kore.Step.Simplification.Or
Description : Tools for Or pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Or
    ( simplifyEvaluated
    , simplify
    ) where

import qualified Data.Functor.Foldable as Recursive

import           Kore.AST.Pure
import           Kore.Predicate.Predicate
                 ( makeOrPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, merge )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser

{-|'simplify' simplifies an 'Or' pattern with 'OrOfExpandedPattern'
children by merging the two children.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => Or level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Or
        { orFirst = first
        , orSecond = second
        }
  =
    simplifyEvaluated first second

{-| simplifies an 'Or' given its two 'OrOfExpandedPattern' children.

See 'simplify' for detailed documentation.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Or level) (Valid level) (OrOfExpandedPattern level variable)

instead of two 'OrOfExpandedPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Valid' annotation will eventually cache information
besides the pattern sort, which will make it even more useful to carry around.

-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplifyEvaluated first second =
    case OrOfExpandedPattern.extractPatterns first of
        [patt] -> halfSimplifyEvaluated patt second
        _ -> case OrOfExpandedPattern.extractPatterns second of
            [patt] -> halfSimplifyEvaluated patt first
            _ -> defaultMerge
  where
    defaultMerge =
        ( OrOfExpandedPattern.merge first second
        , SimplificationProof
        )

-- TODO(virgil): This should do all possible mergings, not just the first
-- term with the second.
halfSimplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
halfSimplifyEvaluated
    Predicated
        { term = term1
        , predicate = predicate1
        , substitution = substitution1
        }
    second
  | _ :< TopPattern _ <- Recursive.project term1
  , pattern2 : patterns <- OrOfExpandedPattern.extractPatterns second
  , Predicated { predicate = predicate2 } <- pattern2
  , Predicated { substitution = substitution2 } <- pattern2
  , Substitution.unwrap substitution1 == Substitution.unwrap substitution2
  =
    ( OrOfExpandedPattern.make
        ( Predicated
            { term = term1
            , predicate = makeOrPredicate predicate1 predicate2
            , substitution = substitution1
            }
        : patterns
        )
    , SimplificationProof
    )
halfSimplifyEvaluated
    first second
  =
    ( OrOfExpandedPattern.merge (OrOfExpandedPattern.make [first]) second
    , SimplificationProof
    )
