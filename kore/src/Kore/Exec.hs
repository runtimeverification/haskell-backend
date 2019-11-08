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
    , extractRules
    , mergeAllRules
    , mergeRulesConsecutiveBatches
    , search
    , prove
    , proveWithRepl
    , boundedModelCheck
    , Rewrite
    , Equality
    ) where

import Control.Concurrent.MVar
import Control.Error.Util
    ( note
    )
import qualified Control.Monad as Monad
import Control.Monad.Catch
    ( MonadCatch
    )
import Control.Monad.IO.Unlift
    ( MonadUnliftIO
    )
import Control.Monad.Trans.Except
    ( runExceptT
    )
import qualified Data.Bifunctor as Bifunctor
    ( first
    , second
    )
import Data.Coerce
    ( Coercible
    , coerce
    )
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )
import qualified Data.Map as Map
import Data.Maybe
    ( mapMaybe
    )
import Data.Proxy
    ( Proxy
    )
import Data.Text
    ( Text
    )
import GHC.Stack
    ( HasCallStack
    )
import System.Exit
    ( ExitCode (..)
    )

import Data.Limit
    ( Limit (..)
    )
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Symbol
    ( StepperAttributes
    )
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
    ( build
    )
import Kore.IndexedModule.Resolvers
    ( resolveInternalSymbol
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( extractPatterns
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import qualified Kore.Logger as Log
import qualified Kore.ModelChecker.Bounded as Bounded
import Kore.Predicate.Predicate
    ( makeMultipleOrPredicate
    , unwrapPredicate
    )
import Kore.Profiler.Data
    ( MonadProfiler
    )
import qualified Kore.Profiler.Profile as Profiler
    ( initialization
    )
import qualified Kore.Repl as Repl
import qualified Kore.Repl.Data as Repl.Data
import Kore.Step
import Kore.Step.Rule
    ( EqualityRule
    , ImplicationRule (..)
    , RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    , extractImplicationClaims
    , extractRewriteAxioms
    , getRewriteRule
    )
import Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    )
import qualified Kore.Step.Rule.Combine as Rules
    ( mergeRules
    , mergeRulesConsecutiveBatches
    )
import Kore.Step.Rule.Expand
    ( ExpandSingleConstructors (..)
    )
import Kore.Step.Rule.Simplify
    ( SimplifyRuleLHS (..)
    )
import Kore.Step.Search
    ( searchGraph
    )
import qualified Kore.Step.Search as Search
import Kore.Step.Simplification.Data
    ( evalSimplifier
    )
import qualified Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.Rule as Rule
import Kore.Step.Simplification.Simplify
    ( BuiltinAndAxiomSimplifierMap
    , MonadSimplify
    , TermLikeSimplifier
    )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Strategies.Goal as Goal
import Kore.Strategies.Verification
    ( Claim
    , CommonProofState
    , verify
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( unparseToText
    )
import SMT
    ( MonadSMT
    , SMT
    )

-- | Configuration used in symbolic execution.
type Config = Pattern Variable

-- | Semantic rule used during execution.
type Rewrite = RewriteRule Variable

-- | Function rule used during execution.
type Equality = EqualityRule Variable

type ExecutionGraph = Strategy.ExecutionGraph Config (RewriteRule Variable)

-- | A collection of rules and simplifiers used during execution.
data Initialized = Initialized { rewriteRules :: ![Rewrite] }

-- | The products of execution: an execution graph, and assorted simplifiers.
data Execution =
    Execution
        { simplifier :: !TermLikeSimplifier
        , axiomIdToSimplifier :: !BuiltinAndAxiomSimplifierMap
        , executionGraph :: !ExecutionGraph
        }

-- | Symbolic execution
exec
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadUnliftIO smt
        )
    => VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike Variable
    -- ^ The input pattern
    -> smt (TermLike Variable)
exec verifiedModule strategy initialTerm =
    evalSimplifier verifiedModule' $ do
        execution <- execute verifiedModule' strategy initialTerm
        let
            Execution { executionGraph } = execution
            finalConfig = pickLongest executionGraph
            finalTerm =
                forceSort patternSort
                $ Pattern.toTermLike finalConfig
        return finalTerm
  where
    verifiedModule' =
        IndexedModule.mapPatterns
            -- TODO (thomas.tuegel): Move this into Kore.Builtin
            (Builtin.internalize metadataTools)
            verifiedModule
    -- It's safe to build the MetadataTools using the external IndexedModule
    -- because MetadataTools doesn't retain any knowledge of the patterns which
    -- are internalized.
    metadataTools = MetadataTools.build verifiedModule
    patternSort = termLikeSort initialTerm

-- | Project the value of the exit cell, if it is present.
execGetExitCode
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadUnliftIO smt
        )
    => VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike Variable
    -- ^ The final pattern (top cell) to extract the exit code
    -> smt ExitCode
execGetExitCode indexedModule strategy' finalTerm =
    case resolveInternalSymbol indexedModule $ noLocationId "LblgetExitCode" of
        Nothing -> return ExitSuccess
        Just mkExitCodeSymbol -> do
            exitCodePattern <-
                -- TODO (thomas.tuegel): Run in original execution context.
                exec indexedModule strategy'
                $ mkApplySymbol (mkExitCodeSymbol []) [finalTerm]
            case exitCodePattern of
                Builtin_ (Domain.BuiltinInt (Domain.InternalInt _ exit))
                  | exit == 0 -> return ExitSuccess
                  | otherwise -> return $ ExitFailure $ fromInteger exit
                _ -> return $ ExitFailure 111

-- | Symbolic search
search
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadUnliftIO smt
        )
    => VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike Variable
    -- ^ The input pattern
    -> Pattern Variable
    -- ^ The pattern to match during execution
    -> Search.Config
    -- ^ The bound on the number of search matches and the search type
    -> smt (TermLike Variable)
search verifiedModule strategy termLike searchPattern searchConfig =
    evalSimplifier verifiedModule $ do
        execution <- execute verifiedModule strategy termLike
        let
            Execution { executionGraph } = execution
            match target config = Search.matchWith target config
        solutionsLists <-
            searchGraph searchConfig (match searchPattern) executionGraph
        let
            solutions = concatMap MultiOr.extractPatterns solutionsLists
            orPredicate =
                makeMultipleOrPredicate (Condition.toPredicate <$> solutions)
        return (forceSort patternSort $ unwrapPredicate orPredicate)
  where
    patternSort = termLikeSort termLike


-- | Proving a spec given as a module containing rules to be proven
prove
    ::  forall claim smt
      . ( Log.WithLog Log.LogMessage smt
        , MonadCatch smt
        , MonadProfiler smt
        , MonadUnliftIO smt
        , MonadSMT smt
        , Claim claim
        , Eq claim
        , Show claim
        , Show (Goal.Rule claim)
        , TopBottom claim
        , Goal.ProofState claim (Pattern Variable) ~ CommonProofState
        )
    => Limit Natural
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> Proxy claim
    -- ^ Proxy for the claim type
    -> smt (Either (TermLike Variable) ())
prove limit definitionModule specModule claimProxy =
    evalProver definitionModule specModule claimProxy
    $ \initialized -> do
        let InitializedProver { axioms, claims } = initialized
        result <-
            runExceptT
            $ verify
                claims
                axioms
                (map (\x -> (x,limit)) (extractUntrustedClaims' claims))
        return $ Bifunctor.first Pattern.toTermLike result
  where
    extractUntrustedClaims' :: [claim] -> [claim]
    extractUntrustedClaims' =
        filter (not . Goal.isTrusted)

-- | Initialize and run the repl with the main and spec modules. This will loop
-- the repl until the user exits.
proveWithRepl
    :: forall claim
     . Claim claim
    => Eq claim
    => TopBottom claim
    => VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> Proxy claim
    -- ^ Proxy for the claim type
    -> MVar (Log.LogAction IO Log.SomeEntry)
    -> Repl.Data.ReplScript
    -- ^ Optional script
    -> Repl.Data.ReplMode
    -- ^ Run in a specific repl mode
    -> Repl.Data.OutputFile
    -- ^ Optional Output file
    -> SMT ()
proveWithRepl
    definitionModule
    specModule
    claimProxy
    mvar
    replScript
    replMode
    outputFile
  =
    evalProver definitionModule specModule claimProxy
    $ \initialized -> do
        let InitializedProver { axioms, claims } = initialized
        Repl.runRepl axioms claims mvar replScript replMode outputFile

-- | Bounded model check a spec given as a module containing rules to be checked
boundedModelCheck
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadUnliftIO smt
        )
    => Limit Natural
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> Strategy.GraphSearchOrder
    -> smt (Bounded.CheckResult (TermLike Variable))
boundedModelCheck limit definitionModule specModule searchOrder =
    evalSimplifier definitionModule $ initialize definitionModule
    $ \initialized -> do
        let Initialized { rewriteRules } = initialized
            specClaims = extractImplicationClaims specModule
        assertSomeClaims specClaims
        assertSingleClaim specClaims
        let
            axioms = fmap Bounded.Axiom rewriteRules
            claims = fmap makeClaim specClaims

        Bounded.checkClaim
            (Bounded.bmcStrategy axioms)
            searchOrder
            (head claims, limit)

-- | Rule merging
mergeAllRules
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadUnliftIO smt
        )
    => VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> [Text]
    -- ^ The list of rules to merge
    -> smt (Either Text [RewriteRule Variable])
mergeAllRules = mergeRules Rules.mergeRules

-- | Rule merging
mergeRulesConsecutiveBatches
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadUnliftIO smt
        )
    => Int
    -- ^ Batch size
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> [Text]
    -- ^ The list of rules to merge
    -> smt (Either Text [RewriteRule Variable])
mergeRulesConsecutiveBatches batchSize =
    mergeRules (Rules.mergeRulesConsecutiveBatches batchSize)

-- | Rule merging in batches
mergeRules
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadUnliftIO smt
        )
    =>  (  NonEmpty (RewriteRule Variable)
        -> Simplifier.SimplifierT smt [RewriteRule Variable]
        )
    -- ^ The rule merger
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> [Text]
    -- ^ The list of rules to merge
    -> smt (Either Text [RewriteRule Variable])
mergeRules ruleMerger verifiedModule ruleNames =
    evalSimplifier verifiedModule
    $ initialize verifiedModule
    $ \initialized -> do
        let Initialized { rewriteRules } = initialized

        let nonEmptyRules :: Either Text (NonEmpty (RewriteRule Variable))
            nonEmptyRules = do
                rules <- extractRules rewriteRules ruleNames
                case rules of
                    [] -> Left "Empty rule list."
                    (r : rs) -> Right (r :| rs)

        case nonEmptyRules of
            (Left left) -> return (Left left)
            (Right rules) -> Right <$> ruleMerger rules

extractRules
    :: [RewriteRule Variable]
    -> [Text]
    -> Either Text [RewriteRule Variable]
extractRules rules = foldr addExtractRule (Right [])
  where
    addExtractRule
        :: Text
        -> Either Text [RewriteRule Variable]
        -> Either Text [RewriteRule Variable]
    addExtractRule ruleName processedRules =
        (:) <$> extractRule ruleName <*> processedRules

    maybeRuleUniqueId :: RewriteRule Variable -> Maybe Text
    maybeRuleUniqueId
        (RewriteRule RulePattern
            { attributes = Attribute.Axiom
                { uniqueId = Attribute.UniqueId maybeName }
            }
        )
      =
        maybeName

    maybeRuleLabel :: RewriteRule Variable -> Maybe Text
    maybeRuleLabel
        (RewriteRule RulePattern
            { attributes = Attribute.Axiom
                { label = Attribute.Label maybeName }
            }
        )
      =
        maybeName

    idRules :: [RewriteRule Variable] -> [(Text, RewriteRule Variable)]
    idRules = mapMaybe namedRule
      where
        namedRule rule = do
            name <- maybeRuleUniqueId rule
            return (name, rule)

    labelRules :: [RewriteRule Variable] -> [(Text, RewriteRule Variable)]
    labelRules = mapMaybe namedRule
      where
        namedRule rule = do
            name <- maybeRuleLabel rule
            return (name, rule)

    rulesByName :: Map.Map Text (RewriteRule Variable)
    rulesByName = Map.union
        (Map.fromList (idRules rules))
        (Map.fromList (labelRules rules))

    extractRule :: Text -> Either Text (RewriteRule Variable)
    extractRule ruleName =
        note
            ("Rule not found: '" <> ruleName <> "'.")
            (Map.lookup ruleName rulesByName)

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

makeClaim
    :: Coercible (RulePattern Variable) claim
    => (Attribute.Axiom, claim) -> claim
makeClaim (attributes, rule) =
    coerce RulePattern
        { attributes = attributes
        , left = left . coerce $ rule
        , antiLeft = antiLeft . coerce $ rule
        , right = right . coerce $ rule
        , requires = requires . coerce $ rule
        , ensures = ensures . coerce $ rule
        }

simplifyRuleOnSecond
    :: (MonadSimplify simplifier, Claim claim)
    => (Attribute.Axiom, claim)
    -> simplifier (Attribute.Axiom, claim)
simplifyRuleOnSecond (atts, rule) = do
    rule' <- Rule.simplifyRewriteRule (RewriteRule . coerce $ rule)
    return (atts, coerce . getRewriteRule $ rule')

-- | Construct an execution graph for the given input pattern.
execute
    :: MonadSimplify simplifier
    => VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> ([Rewrite] -> [Strategy (Prim Rewrite)])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike Variable
    -- ^ The input pattern
    -> simplifier Execution
execute verifiedModule strategy inputPattern =
    Log.withLogScope "setUpConcreteExecution"
    $ initialize verifiedModule $ \initialized -> do
        let Initialized { rewriteRules } = initialized
        simplifier <- Simplifier.askSimplifierTermLike
        axiomIdToSimplifier <- Simplifier.askSimplifierAxioms
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
            , axiomIdToSimplifier
            , executionGraph
            }

-- | Collect various rules and simplifiers in preparation to execute.
initialize
    :: MonadSimplify simplifier
    => VerifiedModule StepperAttributes Attribute.Axiom
    -> (Initialized -> simplifier a)
    -> simplifier a
initialize verifiedModule within = do
    rewriteRules <- Profiler.initialization "simplifyRewriteRule" $
        mapM Rule.simplifyRewriteRule (extractRewriteAxioms verifiedModule)
    let initialized = Initialized { rewriteRules }
    within initialized

data InitializedProver claim =
    InitializedProver
        { axioms :: ![Goal.Rule claim]
        , claims :: ![claim]
        }

data MaybeChanged a = Changed !a | Unchanged !a

fromMaybeChanged :: MaybeChanged a -> a
fromMaybeChanged (Changed a) = a
fromMaybeChanged (Unchanged a) = a

-- | Collect various rules and simplifiers in preparation to execute.
initializeProver
    :: forall simplifier claim a
    .  MonadSimplify simplifier
    => Claim claim
    => Eq claim
    => TopBottom claim
    => VerifiedModule StepperAttributes Attribute.Axiom
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -> (InitializedProver claim -> simplifier a)
    -> simplifier a
initializeProver definitionModule specModule within =
    initialize definitionModule
    $ \initialized -> do
        tools <- Simplifier.askMetadataTools
        let Initialized { rewriteRules } = initialized
            changedSpecClaims
                :: [(Attribute.Axiom, MaybeChanged claim)]
            changedSpecClaims =
                map
                    (Bifunctor.second $ expandClaim tools)
                    (Goal.extractClaims specModule)
            mapMSecond
                :: Monad m
                => (rule -> m [rule'])
                -> (attributes, rule) -> m [(attributes, rule')]
            mapMSecond f (attribute, rule) = do
                simplified <- f rule
                return (map ((,) attribute) simplified)
            simplifyToList
                :: claim -> simplifier [claim]
            simplifyToList rules = do
                simplified <- simplifyRuleLhs rules
                return (MultiAnd.extractPatterns simplified)

        Log.withLogScope (Log.Scope "ExpandedClaim")
            $ mapM_ (logChangedClaim . snd) changedSpecClaims

        let specClaims :: [(Attribute.Axiom, claim)]
            specClaims =
                map (Bifunctor.second fromMaybeChanged) changedSpecClaims

        -- This assertion should come before simplifiying the claims,
        -- since simplification should remove all trivial claims.
        assertSomeClaims specClaims
        simplifiedSpecClaims <-
            mapM (mapMSecond simplifyToList) specClaims
        specAxioms <- Profiler.initialization "simplifyRuleOnSecond"
            $ traverse simplifyRuleOnSecond (concat simplifiedSpecClaims)
        let
            axioms = coerce <$> rewriteRules
            claims = fmap makeClaim specAxioms
            initializedProver = InitializedProver { axioms, claims}
        within initializedProver
  where
    expandClaim
        :: SmtMetadataTools attributes
        -> claim
        -> MaybeChanged claim
    expandClaim tools claim =
        if claim /= expanded
            then Changed expanded
            else Unchanged claim
      where
        expanded = expandSingleConstructors tools claim

    logChangedClaim
        :: HasCallStack
        => MaybeChanged claim
        -> simplifier ()
    logChangedClaim (Changed claim) =
        Log.logInfo ("Claim variables were expanded:\n" <> unparseToText claim)
    logChangedClaim (Unchanged _) = return ()

evalProver
    ::  forall claim smt a
      . ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadUnliftIO smt
        , MonadSMT smt
        , Claim claim
        , Eq claim
        , TopBottom claim
        )
    => VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The main module
    -> VerifiedModule StepperAttributes Attribute.Axiom
    -- ^ The spec module
    -> Proxy claim
    -- ^ Proxy for the claim type
    -> (InitializedProver claim -> Simplifier.SimplifierT smt a)
    -- The prover
    -> smt a
evalProver definitionModule specModule _ prover =
    evalSimplifier definitionModule
    $ initializeProver definitionModule specModule prover
