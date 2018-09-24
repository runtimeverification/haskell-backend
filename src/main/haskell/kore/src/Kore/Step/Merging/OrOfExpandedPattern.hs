{-|
Module      : Kore.Step.Merging.OrOfExpandedPattern
Description : Tools for merging OrOfExpandedPatterns with various stuff.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Merging.OrOfExpandedPattern
    ( mergeWithPredicateSubstitution
    ) where

import           Data.Reflection ( Given )
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution )
import qualified Kore.Step.Merging.ExpandedPattern as ExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..), Simplifier,
                 SimplificationProof (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.SMT.SMT ( SMTAttributes )
{-| 'mergeWithPredicateSubstitution' ands the given predicate/substitution
to the given Or.
-}
mergeWithPredicateSubstitution
    ::  ( MetaOrObject level
        , Given (MetadataTools level SMTAttributes)
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PureMLPatternSimplifier level Variable
    -- ^ Evaluates functions in a pattern.
    -> PredicateSubstitution level Variable
    -- ^ PredicateSubstitution to add.
    -> OrOfExpandedPattern level Variable
    -- ^ Pattern to which the condition should be added.
    -> Simplifier (OrOfExpandedPattern level Variable, SimplificationProof level)
mergeWithPredicateSubstitution
    tools
    simplifier
    toMerge
    patt
  = do
    (evaluated, _proofs) <-
        OrOfExpandedPattern.traverseWithPairs
            (ExpandedPattern.mergeWithPredicateSubstitution
                tools
                simplifier
                toMerge
            )
            patt
    return (evaluated, SimplificationProof)
