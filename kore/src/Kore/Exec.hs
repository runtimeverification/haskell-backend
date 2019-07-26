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
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
                 ( build )
import           Kore.IndexedModule.Resolvers
                 ( resolveSymbol )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import qualified Kore.Logger as Log
import qualified Kore.ModelChecker.Bounded as Bounded
import           Kore.OnePath.Verification
                 ( Axiom (Axiom), Claim, defaultStrategy, verify )
import qualified Kore.OnePath.Verification as Claim
import           Kore.Predicate.Predicate
                 ( makeMultipleOrPredicate, unwrapPredicate )
import qualified Kore.Repl as Repl
import qualified Kore.Repl.Data as Repl.Data
import           Kore.Step
import           Kore.Step.Axiom.EvaluationStrategy
                 ( builtinEvaluation, simplifierWithFallback )
import           Kore.Step.Axiom.Registry
                 ( axiomPatternsToEvaluators, extractEqualityAxioms )
import           Kore.Step.Rule
                 ( EqualityRule, ImplicationRule (..), OnePathRule (..),
                 RewriteRule (RewriteRule), RulePattern (RulePattern),
                 extractImplicationClaims, extractOnePathClaims,
                 extractRewriteAxioms, getRewriteRule )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Search
                 ( searchGraph )
import qualified Kore.Step.Search as Search
import           Kore.Step.Simplification.Data
                 ( BuiltinAndAxiomSimplifierMap, PredicateSimplifier (..),
                 Simplifier, TermLikeSimplifier, evalSimplifier )
import qualified Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.Predicate as Predicate
import qualified Kore.Step.Simplification.Rule as Rule
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import qualified Kore.Step.Strategy as Strategy
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
        execution <- execute indexedModule' strategy initialTerm
        let
            Execution { executionGraph } = execution
            finalConfig = pickLongest executionGraph
            finalTerm =
                forceSort patternSort
                $ Pattern.toTermLike finalConfig
        return finalTerm
  where
    indexedModule' =
        IndexedModule.mapPatterns
            (Builtin.internalize metadataTools)
            indexedModule
    -- It's safe to build the MetadataTools using the external IndexedModule
    -- because MetadataTools doesn't retain any knowledge of the patterns which
    -- are internalized.
    metadataTools = MetadataTools.build indexedModule
    env =
        Simplifier.Env
            { metadataTools
            , simplifierTermLike = emptyTermLikeSimplifier
            , simplifierPredicate = emptyPredicateSimplifier
            , simplifierAxioms = emptyAxiomSimplifiers
            }
    patternSort = termLikeSort initialTerm

emptyAxiomSimplifiers :: BuiltinAndAxiomSimplifierMap
emptyAxiomSimplifiers = Map.empty

emptyTermLikeSimplifier :: TermLikeSimplifier
emptyTermLikeSimplifier = Simplifier.create

emptyPredicateSimplifier :: PredicateSimplifier
emptyPredicateSimplifier = Predicate.create

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
            exitCodePattern <-
                -- TODO (thomas.tuegel): Run in original execution context.
                exec indexedModule strategy'
                $ applySymbol_ exitCodeSymbol [finalTerm]
            case exitCodePattern of
                Builtin_ (Domain.BuiltinInt (Domain.InternalInt _ exit))
                  | exit == 0 -> return ExitSuccess
                  | otherwise -> return $ ExitFailure $ fromInteger exit
                _ -> return $ ExitFailure 111

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
            Execution { executionGraph } = execution
            match target config = Search.matchWith target config
        solutionsLists <-
            searchGraph searchConfig (match searchPattern) executionGraph
        let
            solutions = concatMap MultiOr.extractPatterns solutionsLists
            orPredicate =
                makeMultipleOrPredicate (Predicate.toPredicate <$> solutions)
        return (forceSort patternSort $ unwrapPredicate orPredicate)
  where
    metadataTools = MetadataTools.build verifiedModule
    env =
        Simplifier.Env
            { metadataTools
            , simplifierTermLike = emptyTermLikeSimplifier
            , simplifierPredicate = emptyPredicateSimplifier
            , simplifierAxioms = emptyAxiomSimplifiers
            }
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
    evalSimplifier env $ initialize definitionModule $ \initialized -> do
        let Initialized { rewriteRules } = initialized
            specClaims = extractOnePathClaims specModule
        specAxioms <- traverse simplifyRuleOnSecond specClaims
        assertSomeClaims specAxioms
        let
            axioms = fmap Axiom rewriteRules
            claims = fmap makeClaim specAxioms
        result <-
            runExceptT
            $ verify
                (defaultStrategy claims axioms)
                (map (\x -> (x,limit)) (extractUntrustedClaims claims))
        return $ Bifunctor.first Pattern.toTermLike result
  where
    metadataTools = MetadataTools.build definitionModule
    env =
        Simplifier.Env
            { metadataTools
            , simplifierTermLike = emptyTermLikeSimplifier
            , simplifierPredicate = emptyPredicateSimplifier
            , simplifierAxioms = emptyAxiomSimplifiers
            }

-- | Initialize and run the repl with the main and spec modules. This will loop
-- the repl until the user exits.
proveWithRepl
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> MVar (Log.LogAction IO Log.LogMessage)
    -> Repl.Data.ReplScript
    -- ^ Optional script
    -> Repl.Data.ReplMode
    -- ^ Run in a specific repl mode
    -> Repl.Data.OutputFile
    -- ^ Optional Output file
    -> SMT ()
proveWithRepl definitionModule specModule mvar replScript replMode outputFile =
    evalSimplifier env $ initialize definitionModule $ \initialized -> do
        let Initialized { rewriteRules } = initialized
            specClaims = extractOnePathClaims specModule
        specAxioms <- traverse simplifyRuleOnSecond specClaims
        assertSomeClaims specAxioms
        let
            axioms = fmap Axiom rewriteRules
            claims = fmap makeClaim specAxioms
        Repl.runRepl axioms claims mvar replScript replMode outputFile
  where
    metadataTools = MetadataTools.build definitionModule
    env =
        Simplifier.Env
            { metadataTools
            , simplifierTermLike = emptyTermLikeSimplifier
            , simplifierPredicate = emptyPredicateSimplifier
            , simplifierAxioms = emptyAxiomSimplifiers
            }

-- | Bounded model check a spec given as a module containing rules to be checked
boundedModelCheck
    :: Limit Natural
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> Strategy.GraphSearchOrder
    -> SMT (Bounded.CheckResult (TermLike Variable))
boundedModelCheck limit definitionModule specModule searchOrder =
    evalSimplifier env $ initialize definitionModule $ \initialized -> do
        let Initialized { rewriteRules } = initialized
            specClaims = extractImplicationClaims specModule
        assertSomeClaims specClaims
        assertSingleClaim specClaims
        let
            axioms = fmap Axiom rewriteRules
            claims = fmap makeClaim specClaims

        Bounded.checkClaim
            (Bounded.bmcStrategy axioms)
            searchOrder
            (head claims, limit)
  where
    metadataTools = MetadataTools.build definitionModule
    env =
        Simplifier.Env
            { metadataTools
            , simplifierTermLike = emptyTermLikeSimplifier
            , simplifierPredicate = emptyPredicateSimplifier
            , simplifierAxioms = emptyAxiomSimplifiers
            }

assertSingleClaim :: Monad m => [claim] -> m ()
assertSingleClaim claims =
    Monad.when (length claims > 1) . error
        $ "More than one claim is found in the module."

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
        , left = left . coerce $ rule
        , right = right . coerce $ rule
        , requires = requires . coerce $ rule
        , ensures = ensures . coerce $ rule
        }

simplifyRuleOnSecond
    :: Claim claim
    => (Attribute.Axiom, claim)
    -> Simplifier (Attribute.Axiom, claim)
simplifyRuleOnSecond (atts, rule) = do
    rule' <- Rule.simplifyRewriteRule (RewriteRule . coerce $ rule)
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
execute verifiedModule strategy inputPattern =
    Log.withLogScope "setUpConcreteExecution"
    $ initialize verifiedModule $ \initialized -> do
        let
            Initialized { rewriteRules } = initialized
            Initialized { simplifier } = initialized
            Initialized { substitutionSimplifier } = initialized
            Initialized { axiomIdToSimplifier } = initialized
        simplifiedPatterns <-
            Pattern.simplify (Pattern.fromTermLike inputPattern)
        let
            initialPattern =
                case MultiOr.extractPatterns simplifiedPatterns of
                    [] -> Pattern.bottomOf patternSort
                    (config : _) -> config
              where
                patternSort = termLikeSort inputPattern
            runStrategy' = runStrategy transitionRule (strategy rewriteRules)
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
    -> (Initialized -> Simplifier a)
    -> Simplifier a
initialize verifiedModule within = do
    functionAxioms <-
        Rule.simplifyFunctionAxioms (extractEqualityAxioms verifiedModule)
    rewriteRules <-
        mapM Rule.simplifyRewriteRule (extractRewriteAxioms verifiedModule)
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
        simplifier = Simplifier.create
        substitutionSimplifier = Predicate.create
        initialized =
            Initialized
                { rewriteRules
                , simplifier
                , substitutionSimplifier
                , axiomIdToSimplifier
                }
        locally =
            Simplifier.localSimplifierTermLike (const simplifier)
            . Simplifier.localSimplifierPredicate (const substitutionSimplifier)
            . Simplifier.localSimplifierAxioms (const axiomIdToSimplifier)
    locally (within initialized)
