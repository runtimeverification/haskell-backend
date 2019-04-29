module Kore.Step.Simplification.Ceil
    ( makeEvaluateTerm
    ) where

import Kore.Syntax.Variable
       ( SortedVariable )
import Kore.AST.MetaOrObject
import Kore.Attribute.Symbol
       ( StepperAttributes )
import Kore.IndexedModule.MetadataTools
       ( SmtMetadataTools )
import Kore.Step.Axiom.Data
       ( BuiltinAndAxiomSimplifierMap )
import Kore.Step.OrPredicate
       ( OrPredicate )
import Kore.Step.Simplification.Data
       ( PredicateSimplifier, SimplificationProof, Simplifier,
       TermLikeSimplifier )
import Kore.Step.TermLike
       ( TermLike )
import Kore.Unparser
       ( Unparse )
import Kore.Variables.Fresh
       ( FreshVariable )

makeEvaluateTerm
    ::  forall variable .
        ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier Object
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -> Simplifier (OrPredicate Object variable, SimplificationProof Object)
