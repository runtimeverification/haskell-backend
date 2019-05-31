module Kore.Step.Simplification.AndTerms where

import Kore.Internal.Pattern
       ( Pattern )
import Kore.Internal.TermLike
       ( TermLike )
import Kore.Step.Simplification.Data
       ( BranchT, BuiltinAndAxiomSimplifierMap, PredicateSimplifier, Simplifier
       , TermLikeSimplifier )
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
    => PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> TermLike variable
    -> TermLike variable
    -> BranchT Simplifier (Pattern variable)

termUnification
    ::  forall variable unifier
    .   ( FreshVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> TermLike variable
    -> TermLike variable
    -> unifier (Pattern variable)
