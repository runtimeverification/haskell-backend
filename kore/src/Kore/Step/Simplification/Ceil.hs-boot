module Kore.Step.Simplification.Ceil
    ( makeEvaluateTerm
    ) where

import Kore.AST.Common
       ( SortedVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject, OrdMetaOrObject, ShowMetaOrObject )
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
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier level
    -> TermLikeSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -> Simplifier
        (OrPredicate level variable, SimplificationProof level)
