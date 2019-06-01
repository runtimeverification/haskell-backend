module Kore.Step.Simplification.Ceil
    ( makeEvaluateTerm
    ) where

import Kore.Attribute.Symbol
       ( StepperAttributes )
import Kore.IndexedModule.MetadataTools
       ( SmtMetadataTools )
import Kore.Internal.OrPredicate
       ( OrPredicate )
import Kore.Internal.TermLike
       ( TermLike )
import Kore.Step.Simplification.Data
       ( BuiltinAndAxiomSimplifierMap, PredicateSimplifier, Simplifier,
       TermLikeSimplifier )
import Kore.Syntax.Variable
       ( SortedVariable )
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
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> TermLike variable
    -> Simplifier (OrPredicate variable)
