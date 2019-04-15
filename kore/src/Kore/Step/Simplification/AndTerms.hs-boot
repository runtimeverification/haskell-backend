module Kore.Step.Simplification.AndTerms where

import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject, OrdMetaOrObject, ShowMetaOrObject )
import Kore.Attribute.Symbol
       ( StepperAttributes )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.Axiom.Data
       ( BuiltinAndAxiomSimplifierMap )
import Kore.Step.Pattern
       ( StepPattern )
import Kore.Step.Representation.ExpandedPattern
       ( ExpandedPattern )
import Kore.Step.Simplification.Data
       ( PredicateSubstitutionSimplifier, SimplificationProof, Simplifier,
       StepPatternSimplifier )
import Kore.Unification.Unify
       ( MonadUnify )
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
    :: forall level variable unifier unifierM .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , SortedVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> StepPattern level variable
    -> StepPattern level variable
    -> unifier (ExpandedPattern level variable, SimplificationProof level)
