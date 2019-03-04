{-|
Module      : Kore.Step.Simplification.Application
Description : Tools for Application pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Application
    ( simplify
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.Function.Evaluator
                 ( evaluateApplication )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( fullCrossProduct, traverseFlattenWithPairsGeneric )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

type ExpandedApplication level variable =
    Predicated
        level
        variable
        (CofreeF
            (Application level)
            (Valid (variable level) level)
            (StepPattern level variable)
        )

{-|'simplify' simplifies an 'Application' of 'OrOfExpandedPattern'.

To do that, it first distributes the terms, making it an Or of Application
patterns, each Application having 'ExpandedPattern's as children,
then it simplifies each of those.

Simplifying an Application of ExpandedPattern means merging the children
predicates ans substitutions, applying functions on the Application(terms),
then merging everything into an ExpandedPattern.
-}
simplify
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> CofreeF
        (Application level)
        (Valid (variable level) level)
        (OrOfExpandedPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    (valid :< app)
  = do
    let
        -- The "Propagation Or" inference rule together with
        -- "Propagation Bottom" for the case when a child or is empty.
        orDistributedChildren = OrOfExpandedPattern.fullCrossProduct children
    (unflattenedOr, _proofs) <-
        OrOfExpandedPattern.traverseFlattenWithPairsGeneric
            (makeAndEvaluateApplications
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                valid
                symbol
            )
            orDistributedChildren
    return
        ( unflattenedOr
        , SimplificationProof
        )
  where
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = children
        }
      = app

makeAndEvaluateApplications
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid (variable level) level
    -> SymbolOrAlias level
    -> [ExpandedPattern level variable]
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeAndEvaluateApplications
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    valid
    symbol
    children
  =
    case MetadataTools.symbolOrAliasType tools symbol of
        HeadType.Symbol ->
            makeAndEvaluateSymbolApplications
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                valid
                symbol
                children
        HeadType.Alias -> error "Alias evaluation not implemented yet."

makeAndEvaluateSymbolApplications
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid (variable level) level
    -> SymbolOrAlias level
    -> [ExpandedPattern level variable]
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeAndEvaluateSymbolApplications
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    valid
    symbol
    children
  = do
    (expandedApplication, _proof) <-
        makeExpandedApplication
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            valid
            symbol
            children
    (functionApplication, _proof) <-
        evaluateApplicationFunction
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            expandedApplication
    return (functionApplication, SimplificationProof)

evaluateApplicationFunction
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> ExpandedApplication level variable
    -- ^ The pattern to be evaluated
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
evaluateApplicationFunction
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    Predicated
        { term, predicate, substitution }
  =
    evaluateApplication
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        Predicated { term = (), predicate, substitution }
        term

makeExpandedApplication
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid (variable level) level
    -> SymbolOrAlias level
    -> [ExpandedPattern level variable]
    -> Simplifier
        (ExpandedApplication level variable, SimplificationProof level)
makeExpandedApplication
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    valid
    symbol
    children
  = do
    (   Predicated
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _proof) <-
            mergePredicatesAndSubstitutions
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                (map ExpandedPattern.predicate children)
                (map ExpandedPattern.substitution children)
    return
        ( Predicated
            { term =
                (:<) valid
                    Application
                        { applicationSymbolOrAlias = symbol
                        , applicationChildren =
                            map ExpandedPattern.term children
                        }
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
