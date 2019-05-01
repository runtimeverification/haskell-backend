module Kore.Step.Simplification.AndTerms where

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
import Kore.Syntax.Variable
       ( SortedVariable )
import Kore.Unification.Unify
       ( MonadUnify )
import Kore.Unparser
import Kore.Variables.Fresh
       ( FreshVariable )

termAnd
    :: forall variable .
        ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap Object
    -> TermLike variable
    -> TermLike variable
    -> Simplifier (Pattern variable, SimplificationProof Object)

termUnification
    :: forall variable unifier unifierM .
        ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap Object
    -> TermLike variable
    -> TermLike variable
    -> unifier (Pattern variable, SimplificationProof Object)
