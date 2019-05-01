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
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern )
import           Kore.Step.Pattern as Pattern
                 ( Conditional (..) )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( fullCrossProduct, traverseFlattenWithPairsGeneric )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 TermLikeSimplifier )
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
            (Valid variable level)
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
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from axiom IDs to axiom evaluators
    -> CofreeF
        (Application SymbolOrAlias)
        (Valid variable Object)
        (OrPattern variable)
    -> Simplifier
        ( OrPattern variable
        , SimplificationProof Object
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
        orDistributedChildren = MultiOr.fullCrossProduct children
    (unflattenedOr, _proofs) <-
        MultiOr.traverseFlattenWithPairsGeneric
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
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid variable Object
    -> SymbolOrAlias
    -> [Pattern variable]
    -> Simplifier
        (OrPattern variable, SimplificationProof Object)
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
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid variable Object
    -> SymbolOrAlias
    -> [Pattern variable]
    -> Simplifier
        (OrPattern variable, SimplificationProof Object)
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
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from axiom IDs to axiom evaluators
    -> ExpandedApplication Object variable
    -- ^ The pattern to be evaluated
    -> Simplifier
        (OrPattern variable, SimplificationProof Object)
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
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from axiom IDs to axiom evaluators
    -> Valid variable Object
    -> SymbolOrAlias
    -> [Pattern variable]
    -> Simplifier
        (ExpandedApplication Object variable, SimplificationProof Object)
makeExpandedApplication
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    valid
    symbol
    children
  = do
    (   Conditional
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _proof) <-
            mergePredicatesAndSubstitutions
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                (map Pattern.predicate children)
                (map Pattern.substitution children)
    return
        ( Conditional
            { term =
                (:<) valid
                    Application
                        { applicationSymbolOrAlias = symbol
                        , applicationChildren =
                            map Pattern.term children
                        }
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
