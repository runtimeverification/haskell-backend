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

import qualified Kore.Attribute.Pattern as Attribute
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( fullCrossProduct, mergeAll )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Function.Evaluator
                 ( evaluateApplication )
import           Kore.Step.Simplification.Data
                 ( BranchT, PredicateSimplifier, Simplifier,
                 TermLikeSimplifier )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

type ExpandedApplication variable =
    Conditional
        variable
        (CofreeF
            (Application SymbolOrAlias)
            (Attribute.Pattern variable)
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
        (Attribute.Pattern variable)
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
    -> Attribute.Pattern variable
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
    -> Attribute.Pattern variable
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
    expandedApplications <- BranchT.gather $
        makeExpandedApplication
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            valid
            symbol
            children
    orResults <-
        traverse
            (evaluateApplicationFunction
                tools
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
            )
            expandedApplications
    return (MultiOr.mergeAll orResults)

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
    -> ExpandedApplication variable
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
    -> Attribute.Pattern variable
    -> SymbolOrAlias
    -> [Pattern variable]
    -> BranchT Simplifier (ExpandedApplication variable)
makeExpandedApplication
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    valid
    symbol
    children
  = do
    merged <-
        mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            (map Pattern.predicate children)
            (map Pattern.substitution children)
    let term =
            valid :< Application
                { applicationSymbolOrAlias = symbol
                , applicationChildren = Pattern.term <$> children
                }
    return $ Pattern.withCondition term merged
