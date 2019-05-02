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
    , Application (..)
    ) where

import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Function.Evaluator
                 ( evaluateApplication )
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Step.Pattern as Pattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( fullCrossProduct )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Step.TermLike
import           Kore.Syntax.Application
import           Kore.Unparser
import           Kore.Variables.Fresh

type ExpandedApplication level variable =
    Conditional
        variable
        (CofreeF
            (Application SymbolOrAlias)
            (Valid variable)
            (TermLike variable)
        )

{-|'simplify' simplifies an 'Application' of 'OrPattern'.

To do that, it first distributes the terms, making it an Or of Application
patterns, each Application having 'Pattern's as children,
then it simplifies each of those.

Simplifying an Application of Pattern means merging the children
predicates ans substitutions, applying functions on the Application(terms),
then merging everything into an Pattern.
-}
simplify
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> CofreeF
        (Application SymbolOrAlias)
        (Valid variable)
        (OrPattern variable)
    -> Simplifier (OrPattern variable)
simplify
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    (valid :< app)
  = do
    evaluated <-
        traverse
            (makeAndEvaluateApplications
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                valid
                symbol
            )
            -- The "Propagation Or" inference rule together with
            -- "Propagation Bottom" for the case when a child or is empty.
            (MultiOr.fullCrossProduct children)
    return (OrPattern.flatten evaluated)
  where
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = children
        }
      = app

makeAndEvaluateApplications
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid variable
    -> SymbolOrAlias
    -> [Pattern variable]
    -> Simplifier (OrPattern variable)
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
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid variable
    -> SymbolOrAlias
    -> [Pattern variable]
    -> Simplifier (OrPattern variable)
makeAndEvaluateSymbolApplications
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    valid
    symbol
    children
  = do
    expandedApplication <-
        makeExpandedApplication
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            valid
            symbol
            children
    evaluateApplicationFunction
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        expandedApplication

evaluateApplicationFunction
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> ExpandedApplication Object variable
    -- ^ The pattern to be evaluated
    -> Simplifier (OrPattern variable)
evaluateApplicationFunction
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    Conditional
        { term, predicate, substitution }
  =
    evaluateApplication
        tools
        substitutionSimplifier
        simplifier
        axiomIdToEvaluator
        Conditional { term = (), predicate, substitution }
        term

makeExpandedApplication
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid variable
    -> SymbolOrAlias
    -> [Pattern variable]
    -> Simplifier (ExpandedApplication Object variable)
makeExpandedApplication
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    valid
    symbol
    children
  = do
    (merged, _proof) <-
        mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            (map Pattern.predicate children)
            (map Pattern.substitution children)
    return $ Pattern.withCondition
        ((:<) valid
            Application
                { applicationSymbolOrAlias = symbol
                , applicationChildren =
                    map Pattern.term children
                }
        )
        merged
