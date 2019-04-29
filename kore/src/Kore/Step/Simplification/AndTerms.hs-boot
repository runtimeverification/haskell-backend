module Kore.Step.Simplification.AndTerms where

import Kore.Syntax.Variable
       ( SortedVariable )
import Kore.AST.MetaOrObject
import Kore.Attribute.Symbol
       ( StepperAttributes )
import Kore.IndexedModule.MetadataTools
       ( SmtMetadataTools )
import Kore.Step.Axiom.Data
       ( BuiltinAndAxiomSimplifierMap )
import Kore.Step.Pattern
       ( Pattern )
import Kore.Step.Simplification.Data
       ( PredicateSimplifier, SimplificationProof, Simplifier,
       TermLikeSimplifier )
import Kore.Step.TermLike
       ( TermLike )
import Kore.Unification.Unify
       ( MonadUnify )
import Kore.Unparser
import Kore.Variables.Fresh
       ( FreshVariable )

termAnd
    :: forall level variable .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> TermLike variable
    -> TermLike variable
    -> Simplifier (Pattern level variable, SimplificationProof level)

termUnification
    :: forall level variable unifier unifierM .
        ( MetaOrObject level
        , FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -> BuiltinAndAxiomSimplifierMap level
    -> TermLike variable
    -> TermLike variable
    -> unifier (Pattern level variable, SimplificationProof level)
