module Kore.Step.Substitution where

import           Kore.AST.MetaOrObject
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern
                 ( Predicate )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, TermLikeSimplifier )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unification.Data
                 ( UnificationProof )
import           Kore.Unification.Substitution
                 ( Substitution )
import           Kore.Unification.Unify
                 ( MonadUnify )
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

mergePredicatesAndSubstitutionsExcept
    ::  ( Show variable
        , SortedVariable variable
        , Ord variable
        , Unparse variable
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -> [Syntax.Predicate variable]
    -> [Substitution variable]
    -> unifier
        ( Predicate variable
        , UnificationProof Object variable
        )
