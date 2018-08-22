{-|
Module      : Kore.Simplification.Equals
Description : Tools for Equals pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Equals
    (simplify
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Equals (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkTop )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeIffPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern), substitutionToPredicate )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), toMLPattern, top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-|'simplify' simplifies an 'Equals' pattern made of 'OrOfExpandedPattern's.

This uses the following simplifications
(t = term, s = substitution, p = predicate):

* Equals(a, a) = true
* Equals(p1 and s1, p2 and s2) = Iff(p1 and s1, p2 and s2)
* Equals produces predicates.

Normalization of the compared terms is not implemented yet, so
Equals(a and b, b and a) will not be evaluated to Top.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => Equals level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Equals
        { equalsFirst = first
        , equalsSecond = second
        }
  =
    simplifyEvaluatedEquals first second

simplifyEvaluatedEquals
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => OrOfExpandedPattern level variable
    -> OrOfExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
simplifyEvaluatedEquals first second
  | first == second =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
  -- TODO: Maybe simplify equalities with top and bottom to ceil and floor
  | otherwise =
    case ( firstPatterns, secondPatterns )
      of
        ([firstP], [secondP]) -> makeEvaluateEquals firstP secondP
        _ ->
            makeEvaluateEquals
                (OrOfExpandedPattern.toExpandedPattern first)
                (OrOfExpandedPattern.toExpandedPattern second)
  where
    firstPatterns = OrOfExpandedPattern.extractPatterns first
    secondPatterns = OrOfExpandedPattern.extractPatterns second

makeEvaluateEquals
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> (OrOfExpandedPattern level variable, SimplificationProof level)
makeEvaluateEquals first second
  | first == second =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
    -- TODO: Also attempt bounded variable renamings, comutativity and whatnot
    -- when testing for equality.
makeEvaluateEquals
    ExpandedPattern
        { term = t@(Top_ _)
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    ExpandedPattern
        { term = Top_ _
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = t
            , predicate =
                -- TODO: Remove fst
                fst $ makeIffPredicate
                    -- TODO: Remove fst
                    (fst $ makeAndPredicate
                        firstPredicate
                        (substitutionToPredicate firstSubstitution))
                    -- TODO: Remove fst
                    (fst $ makeAndPredicate
                        secondPredicate
                        (substitutionToPredicate secondSubstitution)
                    )
            , substitution = []
            }
        ]
    , SimplificationProof
    )
makeEvaluateEquals
    first second
  =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkTop
            , predicate =
                makeEqualsPredicate
                    (ExpandedPattern.toMLPattern first)
                    (ExpandedPattern.toMLPattern second)
            , substitution = []
            }
        ]
    , SimplificationProof
    )
