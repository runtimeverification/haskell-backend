{-|
Module      : Kore.Simplification.Or
Description : Tools for Or pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeOrPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, merge )

{-|'simplify' simplifies an 'Or' pattern with 'OrOfExpandedPattern'
children by merging the two children.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => Or level (OrOfExpandedPattern level domain variable)
    ->  ( OrOfExpandedPattern level domain variable
        , ()
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
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level domain variable
    -> OrOfExpandedPattern level domain variable
    ->  ( OrOfExpandedPattern level domain variable
        , ()
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
        , ()
        )

-- TODO(virgil): This should do all possible mergings, not just the first
-- term with the second.
halfSimplifyEvaluated
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level domain variable
    -> OrOfExpandedPattern level domain variable
    ->  ( OrOfExpandedPattern level domain variable
        , ()
        )
halfSimplifyEvaluated
    first@ExpandedPattern
        { term = Top_ _
        , predicate = firstPredicate
        , substitution = []
        }
    second
  =
    case OrOfExpandedPattern.extractPatterns second of
        [] ->
            ( OrOfExpandedPattern.make [first]
            , ()
            )
        ( ExpandedPattern
            { term, predicate, substitution}
         : patts
         ) ->
            let
                (mergedPredicate, _proof) =
                    makeOrPredicate firstPredicate predicate
            in
                ( OrOfExpandedPattern.make
                    ( ExpandedPattern
                        { term = term
                        , predicate = mergedPredicate
                        , substitution = substitution
                        }
                    : patts
                    )
                , ()
                )
halfSimplifyEvaluated
    first second
  =
    ( OrOfExpandedPattern.merge (OrOfExpandedPattern.make [first]) second
    , ()
    )
