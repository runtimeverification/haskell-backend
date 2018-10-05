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

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Or (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SymbolOrAliasSorts )
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

{-|'simplify' simplifies an 'Or' pattern with 'OrOfExpandedPattern'
children by merging the two children.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
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
simplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
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
        , Given (SymbolOrAliasSorts level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
halfSimplifyEvaluated
    first@Predicated
        { term = Top_ _
        , predicate = firstPredicate
        , substitution = []
        }
    second
  =
    case OrOfExpandedPattern.extractPatterns second of
        [] ->
            ( OrOfExpandedPattern.make [first]
            , SimplificationProof
            )
        ( Predicated
            { term, predicate, substitution}
         : patts
         ) ->
            let
                (mergedPredicate, _proof) =
                    makeOrPredicate firstPredicate predicate
            in
                ( OrOfExpandedPattern.make
                    ( Predicated
                        { term = term
                        , predicate = mergedPredicate
                        , substitution = substitution
                        }
                    : patts
                    )
                , SimplificationProof
                )
halfSimplifyEvaluated
    first second
  =
    ( OrOfExpandedPattern.merge (OrOfExpandedPattern.make [first]) second
    , SimplificationProof
    )
