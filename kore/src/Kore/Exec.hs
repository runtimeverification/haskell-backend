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
    , execGetExitCode
    , search
    , prove
    , proveWithRepl
    , boundedModelCheck
    , Rewrite
    , Equality
    ) where

import           Control.Concurrent.MVar
import qualified Control.Monad as Monad
import           Control.Monad.Trans.Except
                 ( runExceptT )
import qualified Data.Bifunctor as Bifunctor
import           Data.Coerce
                 ( coerce )
import qualified Data.Map.Strict as Map
import           System.Exit
                 ( ExitCode (..) )

import           Data.Limit
                 ( Limit (..) )
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
                 ( build )
import           Kore.IndexedModule.Resolvers
                 ( resolveSymbol )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import qualified Kore.Logger as Log
import qualified Kore.ModelChecker.Bounded as Bounded
import           Kore.OnePath.Verification
                 ( Axiom (Axiom), Claim, defaultStrategy, verify )
import qualified Kore.OnePath.Verification as Claim
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeMultipleOrPredicate,
                 unwrapPredicate )
import qualified Kore.Repl as Repl
import           Kore.Step
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Axiom.EvaluationStrategy
                 ( builtinEvaluation, simplifierWithFallback )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import           Kore.Step.Axiom.Registry
                 ( axiomPatternsToEvaluators, extractEqualityAxioms )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), OnePathRule (..),
                 RewriteRule (RewriteRule), RulePattern (RulePattern),
                 extractImplicationClaims, extractOnePathClaims,
                 extractRewriteAxioms, getRewriteRule )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Search
                 ( searchGraph )
import qualified Kore.Step.Search as Search
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier (..), Simplifier, TermLikeSimplifier,
                 evalSimplifier )
import qualified Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.Predicate as Predicate
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Unification.Substitution as Substitution
import           SMT
                 ( SMT )

-- | Configuration used in symbolic execution.
type Config = Pattern Variable

-- | Semantic rule used during execution.
type Rewrite = RewriteRule Variable

-- | Function rule used during execution.
type Equality = EqualityRule Variable

type ExecutionGraph = Strategy.ExecutionGraph Config (RewriteRule Variable)

-- | A collection of rules and simplifiers used during execution.
data Initialized =
    Initialized
        { rewriteRules :: ![Rewrite]
        , simplifier :: !TermLikeSimplifier
        , substitutionSimplifier :: !PredicateSimplifier
        , axiomIdToSimplifier :: !BuiltinAndAxiomSimplifierMap
        }

-- | The products of execution: an execution graph, and assorted simplifiers.
data Execution =
    Execution
        { simplifier :: !TermLikeSimplifier
        , substitutionSimplifier :: !PredicateSimplifier
        , axiomIdToSimplifier :: !BuiltinAndAxiomSimplifierMap
        , executionGraph :: !ExecutionGraph
        }

-- | Symbolic execution
exec
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike Variable
    -- ^ The input pattern
    -> SMT (TermLike Variable)
exec indexedModule strategy initialTerm =
    evalSimplifier env $ do
        execution <- execute indexedModule strategy initialTerm
        let
            Execution { executionGraph } = execution
            finalConfig = pickLongest executionGraph
            finalTerm =
                forceSort patternSort
                $ Pattern.toTermLike finalConfig
        return finalTerm
  where
    metadataTools = MetadataTools.build indexedModule
    env = Simplifier.Env { metadataTools }
    patternSort = termLikeSort initialTerm

-- | Project the value of the exit cell, if it is present.
execGetExitCode
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike Variable
    -- ^ The final pattern (top cell) to extract the exit code
    -> SMT ExitCode
execGetExitCode indexedModule strategy' finalTerm =
    case resolveSymbol indexedModule $ noLocationId "LblgetExitCode" of
        Left _ -> return ExitSuccess
        Right (_,  exitCodeSymbol) -> do
            exitCodePattern <- exec indexedModule strategy'
                $ applySymbol_ exitCodeSymbol [finalTerm]
            case exitCodePattern of
                Builtin_ (Domain.BuiltinInt (Domain.InternalInt _ 0)) ->
                    return ExitSuccess
                Builtin_ (Domain.BuiltinInt (Domain.InternalInt _ exit)) ->
                    return $ ExitFailure $ fromInteger exit
                _ ->
                    return $ ExitFailure 111

-- | Symbolic search
search
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike Variable
    -- ^ The input pattern
    -> Pattern Variable
    -- ^ The pattern to match during execution
    -> Search.Config
    -- ^ The bound on the number of search matches and the search type
    -> SMT (TermLike Variable)
search verifiedModule strategy termLike searchPattern searchConfig =
    evalSimplifier env $ do
        execution <- execute verifiedModule strategy termLike
        let
            Execution { simplifier, substitutionSimplifier } = execution
            Execution { axiomIdToSimplifier } = execution
            Execution { executionGraph } = execution
            match target config =
                Search.matchWith
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
                    (Predicate.toPredicate <$> solutions)
        return (forceSort patternSort $ unwrapPredicate orPredicate)
  where
    metadataTools = MetadataTools.build verifiedModule
    env = Simplifier.Env { metadataTools }
    patternSort = termLikeSort termLike


-- | Proving a spec given as a module containing rules to be proven
prove
    :: Limit Natural
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> SMT (Either (TermLike Variable) ())
prove limit definitionModule specModule =
    evalSimplifier env $ do
        Initialized
            { rewriteRules
            , simplifier
            , substitutionSimplifier
            , axiomIdToSimplifier
            } <-
                initialize definitionModule
        let specClaims = extractOnePathClaims specModule
        specAxioms <- traverse simplifyRuleOnSecond specClaims
        assertSomeClaims specAxioms
        let
            axioms = fmap Axiom rewriteRules
            claims = fmap makeClaim specAxioms

        result <-
            runExceptT
            $ verify
                simplifier
                substitutionSimplifier
                axiomIdToSimplifier
                (defaultStrategy claims axioms)
                (map (\x -> (x,limit)) (extractUntrustedClaims claims))
        return $ Bifunctor.first Pattern.toTermLike result
  where
    metadataTools = MetadataTools.build definitionModule
    env = Simplifier.Env { metadataTools }

-- | Initialize and run the repl with the main and spec modules. This will loop
-- the repl until the user exits.
proveWithRepl
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> MVar (Log.LogAction IO Log.LogMessage)
    -> Repl.ReplScript
    -- ^ Optional script
    -> Repl.ReplMode
    -- ^ Run in a specific repl mode
    -> SMT ()
proveWithRepl definitionModule specModule mvar replScript replMode =
    evalSimplifier env $ do
        Initialized
            { rewriteRules
            , simplifier
            , substitutionSimplifier
            , axiomIdToSimplifier
            } <- initialize definitionModule
        let specClaims = extractOnePathClaims specModule
        specAxioms <- traverse simplifyRuleOnSecond specClaims
        assertSomeClaims specAxioms
        let
            axioms = fmap Axiom rewriteRules
            claims = fmap makeClaim specAxioms

        Repl.runRepl
            simplifier
            substitutionSimplifier
            axiomIdToSimplifier
            axioms
            claims
            mvar
            replScript
            replMode
  where
    metadataTools = MetadataTools.build definitionModule
    env = Simplifier.Env { metadataTools }

-- | Bounded model check a spec given as a module containing rules to be checked
boundedModelCheck
    :: Limit Natural
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> Strategy.GraphSearchOrder
    -> SMT [Bounded.CheckResult]
boundedModelCheck limit definitionModule specModule searchOrder =
    evalSimplifier env $ do
        Initialized
            { rewriteRules
            , simplifier
            , substitutionSimplifier
            , axiomIdToSimplifier
            } <-
                initialize definitionModule
        let
            axioms = fmap Axiom rewriteRules
            specAxioms = fmap snd $ extractImplicationClaims specModule

        Bounded.check
            simplifier
            substitutionSimplifier
            axiomIdToSimplifier
            (Bounded.bmcStrategy axioms)
            searchOrder
            (map (\x -> (x,limit)) specAxioms)
  where
    metadataTools = MetadataTools.build definitionModule
    env = Simplifier.Env { metadataTools }

assertSomeClaims :: Monad m => [claim] -> m ()
assertSomeClaims claims =
    Monad.when (null claims) . error
        $   "Unexpected empty set of claims.\n"
        ++  "Possible explanation: the frontend and the backend don't agree "
        ++  "on the representation of claims."

makeClaim :: Claim claim => (Attribute.Axiom, claim) -> claim
makeClaim (attributes, rule) =
    coerce RulePattern
        { attributes = attributes
        , left = (left . coerce $ rule)
        , right = (right . coerce $ rule)
        , requires = (requires . coerce $ rule)
        , ensures = (ensures . coerce $ rule)
        }

simplifyRuleOnSecond
    :: Claim claim
    => (Attribute.Axiom, claim)
    -> Simplifier (Attribute.Axiom, claim)
simplifyRuleOnSecond (atts, rule) = do
    rule' <- simplifyRewriteRule (RewriteRule . coerce $ rule)
    return (atts, coerce . getRewriteRule $ rule')

extractUntrustedClaims :: Claim claim => [claim] -> [Rewrite]
extractUntrustedClaims =
    map (RewriteRule . coerce) . filter (not . Claim.isTrusted)

-- | Construct an execution graph for the given input pattern.
execute
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike Variable
    -- ^ The input pattern
    -> Simplifier Execution
execute verifiedModule strategy inputPattern
  = Log.withLogScope "setUpConcreteExecution" $ do
    initialized <- initialize verifiedModule
    let
        Initialized { rewriteRules } = initialized
        Initialized { simplifier } = initialized
        Initialized { substitutionSimplifier } = initialized
        Initialized { axiomIdToSimplifier } = initialized
    simplifiedPatterns <-
        Pattern.simplify
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            (Pattern.fromTermLike inputPattern)
    let
        initialPattern =
            case MultiOr.extractPatterns simplifiedPatterns of
                [] -> Pattern.bottomOf patternSort
                (config : _) -> config
          where
            patternSort = termLikeSort inputPattern
        runStrategy' pat =
            runStrategy
                (transitionRule
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                )
                (strategy rewriteRules)
                pat
    executionGraph <- runStrategy' initialPattern
    return Execution
        { simplifier
        , substitutionSimplifier
        , axiomIdToSimplifier
        , executionGraph
        }

-- | Collect various rules and simplifiers in preparation to execute.
initialize
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> Simplifier Initialized
initialize verifiedModule = do
    tools <- Simplifier.askMetadataTools
    functionAxioms <-
        simplifyFunctionAxioms (extractEqualityAxioms verifiedModule)
    rewriteRules <-
        mapM simplifyRewriteRule (extractRewriteAxioms verifiedModule)
    let
        functionEvaluators :: BuiltinAndAxiomSimplifierMap
        functionEvaluators =
            axiomPatternsToEvaluators functionAxioms
        axiomIdToSimplifier :: BuiltinAndAxiomSimplifierMap
        axiomIdToSimplifier =
            Map.unionWith
                simplifierWithFallback
                -- builtin functions
                (Map.map builtinEvaluation
                    (Builtin.koreEvaluators verifiedModule)
                )
                -- user-defined functions
                functionEvaluators
        simplifier :: TermLikeSimplifier
        simplifier = Simplifier.create axiomIdToSimplifier
        substitutionSimplifier
            :: PredicateSimplifier
        substitutionSimplifier =
            Predicate.create
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
    :: Map.Map (AxiomIdentifier) [Equality]
    -> Simplifier (Map.Map (AxiomIdentifier) [Equality])
simplifyFunctionAxioms =
    (traverse . traverse) simplifyEqualityRule
  where
      simplifyEqualityRule (EqualityRule rule) =
        EqualityRule <$> simplifyRulePattern rule
{- | Simplify a 'Rule' using only matching logic rules.

See also: 'simplifyRulePattern'

 -}
simplifyRewriteRule :: Rewrite -> Simplifier Rewrite
simplifyRewriteRule (RewriteRule rule) =
    RewriteRule <$> simplifyRulePattern rule

{- | Simplify a 'RulePattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.

 -}
simplifyRulePattern
    :: RulePattern Variable
    -> Simplifier (RulePattern Variable)
simplifyRulePattern rulePattern = do
    let RulePattern { left } = rulePattern
    simplifiedLeft <- simplifyPattern left
    case MultiOr.extractPatterns simplifiedLeft of
        [ Conditional { term, predicate, substitution } ]
          | PredicateTrue <- predicate -> do
            let subst = Substitution.toMap substitution
                left' = substitute subst term
                right' = substitute subst right
                  where
                    RulePattern { right } = rulePattern
                requires' = substitute subst <$> requires
                  where
                    RulePattern { requires } = rulePattern
                ensures' = substitute subst <$> ensures
                  where
                    RulePattern { ensures } = rulePattern
                RulePattern { attributes } = rulePattern
            return RulePattern
                { left = left'
                , right = right'
                , requires = requires'
                , ensures = ensures'
                , attributes = attributes
                }
        _ ->
            -- Unable to simplify the given rule pattern, so we return the
            -- original pattern in the hope that we can do something with it
            -- later.
            return rulePattern

-- | Simplify a 'TermLike' using only matching logic rules.
simplifyPattern :: TermLike Variable -> Simplifier (OrPattern Variable)
simplifyPattern termLike = do
    tools <- Simplifier.askMetadataTools
    let
        emptySimplifier = Simplifier.create Map.empty
        emptySubstitutionSimplifier =
            Predicate.create tools emptySimplifier Map.empty
    Pattern.simplify
        emptySubstitutionSimplifier
        emptySimplifier
        Map.empty
        (Pattern.fromTermLike termLike)
