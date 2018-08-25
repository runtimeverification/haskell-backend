{-|
Module      : Kore.Simplification.And
Description : Tools for And pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.And
    ( makeEvaluate
    , simplify
    , simplifyEvaluated
    ) where

import Data.Reflection
       ( Given, give )

import           Kore.AST.Common
                 ( And (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTUtils.SmartConstructors
                 ( mkAnd )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_, pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SortTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), bottom, isBottom, isTop )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( crossProductGenericF, filterOr, isFalse, isTrue, make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh.IntCounter
                 ( IntCounter )
import           Kore.Variables.Int
                 ( IntVariable (..) )

{-|'simplify' simplifies an 'And' of 'OrOfExpandedPattern'.

To do that, it first distributes the terms, making it an Or of And patterns,
each And having 'ExpandedPattern's as children, then it simplifies each of
those.

Since an ExpandedPattern is of the form term /\ predicate /\ substitution,
making an and between two ExpandedPatterns roughly means and-ing each of their
components separately.

This means that a bottom component anywhere makes the result bottom, while
top can always be ignored.

And on terms can sometimes be more interesting, e.g. an and between a variable
and a functional term can be considered a substitution. However, this is not
implemented yet.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> And level (OrOfExpandedPattern level variable)
    -> IntCounter
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    And
        { andFirst = first
        , andSecond = second
        }
  =
    simplifyEvaluated tools first second

{-| simplifies an And given its two 'OrOfExpandedPattern' children.

See 'simplify' for details.
-}
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> IntCounter
        (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluated tools first second
  | OrOfExpandedPattern.isFalse first =
    return (OrOfExpandedPattern.make [], SimplificationProof)
  | OrOfExpandedPattern.isFalse second =
    return (OrOfExpandedPattern.make [], SimplificationProof)

  | OrOfExpandedPattern.isTrue first =
    return (second, SimplificationProof)
  | OrOfExpandedPattern.isTrue second =
    return (first, SimplificationProof)

  | otherwise = do
    orWithProof <- OrOfExpandedPattern.crossProductGenericF
        (makeEvaluate tools) first second
    return
        -- TODO: It's not obvious at all when filtering occurs and when it doesn't.
        ( OrOfExpandedPattern.filterOr
            -- TODO: Remove fst.
            (fst <$> orWithProof)
        , SimplificationProof
        )

{-|'makeEvaluate' simplifies an 'And' of 'ExpandedPattern's.

See the comment for 'simplify' to find more details.
-}
makeEvaluate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> IntCounter (ExpandedPattern level variable, SimplificationProof level)
makeEvaluate
    tools first second
  | ExpandedPattern.isBottom first || ExpandedPattern.isBottom second =
    return (ExpandedPattern.bottom, SimplificationProof)
  | ExpandedPattern.isTop first =
    return (second, SimplificationProof)
  | ExpandedPattern.isTop second =
    return (first, SimplificationProof)
  | otherwise =
    makeEvaluateNonBool tools first second

makeEvaluateNonBool
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> IntCounter (ExpandedPattern level variable, SimplificationProof level)
makeEvaluateNonBool
    tools
    ExpandedPattern
        { term = firstTerm
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    ExpandedPattern
        { term = secondTerm
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  = do -- IntCounter monad
    (   PredicateSubstitution
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _proof
        ) <- mergePredicatesAndSubstitutions
            tools
            [firstPredicate, secondPredicate]
            [firstSubstitution, secondSubstitution]
    return
        ( ExpandedPattern
            { term = give sortTools $ makeTermAnd firstTerm secondTerm
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
  where
    sortTools = MetadataTools.sortTools tools

makeTermAnd
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> PureMLPattern level variable
makeTermAnd b@(Bottom_ _) _ = b
makeTermAnd (Top_ _) term = term
-- TODO: (partial) unification / other simplifications
makeTermAnd first second = makeTermAndSecond first second

makeTermAndSecond
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => PureMLPattern level variable
    -> PureMLPattern level variable
    -> PureMLPattern level variable
makeTermAndSecond _ b@(Bottom_ _) = b
makeTermAndSecond term (Top_ _) = term
-- TODO: (partial) unification / other simplifications
makeTermAndSecond first second = mkAnd first second
