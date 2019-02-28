module Kore.Step.Simplification.Ceil
    ( makeEvaluateTerm
    ) where

import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject, OrdMetaOrObject, ShowMetaOrObject )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.Function.Data
       ( BuiltinAndAxiomSimplifierMap )
import Kore.Step.OrOfExpandedPattern
       ( OrOfPredicateSubstitution )
import Kore.Step.Pattern
       ( StepPattern )
import Kore.Step.Simplification.Data
       ( PredicateSubstitutionSimplifier, SimplificationProof, Simplifier,
       StepPatternSimplifier )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Unparser
       ( Unparse )
import Kore.Variables.Fresh
       ( FreshVariable )

makeEvaluateTerm
    ::  forall level variable .
        ( MetaOrObject level
        , FreshVariable variable
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , Unparse (variable level)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> StepPattern level variable
    -> Simplifier
        (OrOfPredicateSubstitution level variable, SimplificationProof level)
