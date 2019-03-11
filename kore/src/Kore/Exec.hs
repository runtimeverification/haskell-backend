{-|
Module      : Kore.Exec
Description : Expose concrete execution as a library
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Stability   : experimental
Portability : portable

Expose concrete execution as a library
-}
module Kore.Exec
    ( exec
    , search
    , prove
    , Rewrite
    , Equality
    ) where

import           Control.Comonad
import           Control.Monad.Trans.Except
                 ( runExceptT )
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Map.Strict as Map

import           Data.Limit
                 ( Limit (..) )
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                 ( Object (..) )
import           Kore.AST.Valid
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), extractMetadataTools )
import qualified Kore.Logger as Log
import           Kore.OnePath.Verification
                 ( Axiom (Axiom), Claim (Claim), defaultStrategy, verify )
import qualified Kore.OnePath.Verification as Claim
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeMultipleOrPredicate,
                 unwrapPredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Axiom.EvaluationStrategy
                 ( builtinEvaluation, simplifierWithFallback )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import           Kore.Step.Axiom.Registry
                 ( axiomPatternsToEvaluators, extractEqualityAxioms )
import           Kore.Step.AxiomPatterns
                 ( EqualityRule (EqualityRule), RewriteRule (RewriteRule),
                 RulePattern (RulePattern), extractRewriteAxioms,
                 extractRewriteClaims )
import           Kore.Step.AxiomPatterns as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.BaseStep
                 ( StepProof )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.ExpandedPattern as Predicated
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Search
                 ( searchGraph )
import qualified Kore.Step.Search as Search
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 SimplificationProof (..), Simplifier, StepPatternSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.Step
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Step.Strategy
                 ( ExecutionGraph )
import qualified Kore.Unification.Substitution as Substitution

-- | Configuration used in symbolic execution.
type Config = CommonExpandedPattern Object

-- | Proof returned by symbolic execution.
type Proof = StepProof Object Variable

-- | Semantic rule used during execution.
type Rewrite = RewriteRule Object Variable

-- | Function rule used during execution
type Equality = EqualityRule Object Variable

-- | A collection of rules and simplifiers used during execution.
data Initialized =
    Initialized
        { rewriteRules :: ![Rewrite]
        , simplifier :: !(StepPatternSimplifier Object)
        , substitutionSimplifier :: !(PredicateSubstitutionSimplifier Object)
        , axiomIdToSimplifier :: !(BuiltinAndAxiomSimplifierMap Object)
        }

-- | The products of execution: an execution graph, and assorted simplifiers.
data Execution =
    Execution
        { metadataTools :: !(MetadataTools Object StepperAttributes)
        , simplifier :: !(StepPatternSimplifier Object)
        , substitutionSimplifier :: !(PredicateSubstitutionSimplifier Object)
        , axiomIdToSimplifier :: !(BuiltinAndAxiomSimplifierMap Object)
        , executionGraph :: !(ExecutionGraph (Config, Proof))
        }

-- | Symbolic execution
exec
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> CommonStepPattern Object
    -- ^ The input pattern
    -> Simplifier (CommonStepPattern Object)
exec indexedModule strategy purePattern = do
    execution <- execute indexedModule strategy purePattern
    let
        Execution { executionGraph } = execution
        (finalConfig, _) = pickLongest executionGraph
    return (forceSort patternSort $ ExpandedPattern.toMLPattern finalConfig)
  where
    Valid { patternSort } = extract purePattern

-- | Symbolic search
search
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> CommonStepPattern Object
    -- ^ The input pattern
    -> CommonExpandedPattern Object
    -- ^ The pattern to match during execution
    -> Search.Config
    -- ^ The bound on the number of search matches and the search type
    -> Simplifier (CommonStepPattern Object)
search verifiedModule strategy purePattern searchPattern searchConfig = do
    execution <- execute verifiedModule strategy purePattern
    let
        Execution { metadataTools } = execution
        Execution { simplifier, substitutionSimplifier } = execution
        Execution { axiomIdToSimplifier } = execution
        Execution { executionGraph } = execution
        match target (config, _proof) =
            Search.matchWith
                metadataTools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                target
                config
    solutionsLists <-
        searchGraph searchConfig (match searchPattern) executionGraph
    let
        solutions =
            concatMap MultiOr.extractPatterns solutionsLists
        orPredicate =
            makeMultipleOrPredicate
                (Predicated.toPredicate <$> solutions)
    return (forceSort patternSort $ unwrapPredicate orPredicate)
  where
    Valid { patternSort } = extract purePattern

-- | Proving a spec given as a module containing rules to be proven
prove
    :: Limit Natural
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> Simplifier (Either (CommonStepPattern Object) ())
prove limit definitionModule specModule = do
    let
        tools = extractMetadataTools definitionModule
    Initialized
        { rewriteRules
        , simplifier
        , substitutionSimplifier
        , axiomIdToSimplifier
        } <-
            initialize definitionModule tools
    specAxioms <-
        mapM (simplifyRuleOnSecond tools)
            (extractRewriteClaims Object specModule)
    let
        axioms = fmap Axiom rewriteRules
        claims = fmap makeClaim specAxioms

    result <-
        runExceptT
        $ verify
            tools
            simplifier
            substitutionSimplifier
            axiomIdToSimplifier
            (defaultStrategy claims axioms)
            (map (\x -> (x,limit)) (extractUntrustedClaims claims))
    return $ Bifunctor.first OrOfExpandedPattern.toStepPattern result

  where
    makeClaim (attributes, rule) = Claim { rule , attributes }
    simplifyRuleOnSecond
        :: MetadataTools Object StepperAttributes
        -> (Attribute.Axiom, Rewrite)
        -> Simplifier (Attribute.Axiom, Rewrite)
    simplifyRuleOnSecond tools (atts, rule) = do
        rule' <- simplifyRewriteRule tools rule
        return (atts, rule')
    extractUntrustedClaims :: [Claim Object] -> [Rewrite]
    extractUntrustedClaims = map Claim.rule . filter (not . Claim.isTrusted)

-- | Construct an execution graph for the given input pattern.
execute
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> CommonStepPattern Object
    -- ^ The input pattern
    -> Simplifier Execution
execute verifiedModule strategy inputPattern
  = Log.withLogScope "setUpConcreteExecution" $ do
    let metadataTools = extractMetadataTools verifiedModule
    initialized <- initialize verifiedModule metadataTools
    let
        Initialized { rewriteRules } = initialized
        Initialized { simplifier } = initialized
        Initialized { substitutionSimplifier } = initialized
        Initialized { axiomIdToSimplifier } = initialized
    (simplifiedPatterns, _) <-
        ExpandedPattern.simplify
            metadataTools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            (ExpandedPattern.fromPurePattern inputPattern)
    let
        initialPattern =
            case MultiOr.extractPatterns simplifiedPatterns of
                [] -> ExpandedPattern.bottomOf patternSort
                (config : _) -> config
          where
            Valid { patternSort } = extract inputPattern
        runStrategy' pat =
            runStrategy
                (transitionRule
                    metadataTools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                )
                (strategy rewriteRules)
                (pat, mempty)
    executionGraph <- runStrategy' initialPattern
    return Execution
        { metadataTools
        , simplifier
        , substitutionSimplifier
        , axiomIdToSimplifier
        , executionGraph
        }

-- | Collect various rules and simplifiers in preparation to execute.
initialize
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> MetadataTools Object StepperAttributes
    -> Simplifier Initialized
initialize verifiedModule tools =
    do
        functionAxioms <-
            simplifyFunctionAxioms tools
                (extractEqualityAxioms Object verifiedModule)
        rewriteRules <-
            mapM (simplifyRewriteRule tools)
                (extractRewriteAxioms Object verifiedModule)
        let
            functionEvaluators :: BuiltinAndAxiomSimplifierMap Object
            functionEvaluators =
                axiomPatternsToEvaluators functionAxioms
            axiomIdToSimplifier :: BuiltinAndAxiomSimplifierMap Object
            axiomIdToSimplifier =
                Map.unionWith
                    simplifierWithFallback
                    -- builtin functions
                    (Map.map builtinEvaluation
                        (Builtin.koreEvaluators verifiedModule)
                    )
                    -- user-defined functions
                    functionEvaluators
            simplifier :: StepPatternSimplifier Object
            simplifier = Simplifier.create tools axiomIdToSimplifier
            substitutionSimplifier
                :: PredicateSubstitutionSimplifier Object
            substitutionSimplifier =
                PredicateSubstitution.create
                    tools simplifier axiomIdToSimplifier
        return Initialized
            { rewriteRules
            , simplifier
            , substitutionSimplifier
            , axiomIdToSimplifier
            }

{- | Simplify a 'Map' of 'EqualityRule's using only matching logic rules.

See also: 'simplifyRulePattern'

 -}
simplifyFunctionAxioms
    :: MetadataTools Object StepperAttributes
    -> Map.Map (AxiomIdentifier Object) [Equality]
    -> Simplifier (Map.Map (AxiomIdentifier Object) [Equality])
simplifyFunctionAxioms tools = mapM (mapM simplifyEqualityRule)
  where
    simplifyEqualityRule (EqualityRule rule) =
        EqualityRule <$> simplifyRulePattern tools rule

{- | Simplify a 'Rule' using only matching logic rules.

See also: 'simplifyRulePattern'

 -}
simplifyRewriteRule
    :: MetadataTools Object StepperAttributes
    -> Rewrite
    -> Simplifier Rewrite
simplifyRewriteRule tools (RewriteRule rule) =
    RewriteRule <$> simplifyRulePattern tools rule

{- | Simplify a 'RulePattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.

 -}
simplifyRulePattern
    :: MetadataTools Object StepperAttributes
    -> RulePattern Object Variable
    -> Simplifier (RulePattern Object Variable)
simplifyRulePattern tools rulePattern = do
    let RulePattern { left } = rulePattern
    (simplifiedLeft, _proof) <- simplifyPattern tools left
    case MultiOr.extractPatterns simplifiedLeft of
        [ Predicated { term, predicate, substitution } ]
          | PredicateTrue <- predicate -> do
            let subst = Substitution.toMap substitution
                left' = substitute subst term
                right' = substitute subst right
                  where
                    RulePattern { right } = rulePattern
                requires' = substitute subst <$> requires
                  where
                    RulePattern { requires } = rulePattern
                RulePattern { attributes } = rulePattern
            return RulePattern
                { left = left'
                , right = right'
                , requires = requires'
                , attributes = attributes
                }
        _ ->
            -- Unable to simplify the given rule pattern, so we return the
            -- original pattern in the hope that we can do something with it
            -- later.
            return rulePattern

-- | Simplify a 'StepPattern' using only matching logic rules.
simplifyPattern
    :: MetadataTools Object StepperAttributes
    -> CommonStepPattern Object
    -> Simplifier
        (OrOfExpandedPattern Object Variable, SimplificationProof Object)
simplifyPattern tools =
    ExpandedPattern.simplify
        tools
        emptySubstitutionSimplifier
        emptySimplifier
        Map.empty
    . ExpandedPattern.fromPurePattern
  where
    emptySimplifier :: StepPatternSimplifier Object
    emptySimplifier = Simplifier.create tools Map.empty
    emptySubstitutionSimplifier =
        PredicateSubstitution.create tools emptySimplifier Map.empty
