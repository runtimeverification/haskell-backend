module Kore.Step.Simplification.AndTerms where

import Control.Error
       ( ExceptT )

import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject, OrdMetaOrObject, ShowMetaOrObject )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.ExpandedPattern
       ( ExpandedPattern )
import Kore.Step.Function.Data
       ( BuiltinAndAxiomSimplifierMap )
import Kore.Step.Pattern
       ( StepPattern )
import Kore.Step.Simplification.Data
       ( PredicateSubstitutionSimplifier, SimplificationProof, Simplifier,
       StepPatternSimplifier, StepPatternSimplifier )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Unification.Error
       ( UnificationOrSubstitutionError )
import Kore.Unparser
import Kore.Variables.Fresh
       ( FreshVariable )

termAnd
    :: forall level variable .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> StepPattern level variable
    -> StepPattern level variable
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)

termUnification
    :: forall level variable err .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , err ~ ExceptT (UnificationOrSubstitutionError level variable)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> StepPattern level variable
    -> StepPattern level variable
    -> err Simplifier
        (ExpandedPattern level variable, SimplificationProof level)
