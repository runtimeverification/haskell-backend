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

import Prelude.Kore

import Control.Concurrent.MVar
import Control.Error.Util
    ( note
    )
import Control.Monad
    ( (>=>)
    )
import Control.Monad.Catch
    ( MonadCatch
    , MonadThrow
    )
import Control.Monad.Trans.Except
    ( runExceptT
    )
import Data.Coerce
    ( coerce
    )
import Data.Foldable
    ( find
    , traverse_
    )
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
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
import Kore.Equation
    ( Equation
    )
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
import Kore.Internal.Predicate
    ( makeMultipleOrPredicate
    , unwrapPredicate
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    , topTODO
    )
import Kore.Internal.TermLike
import Kore.Log.ErrorRewriteLoop
    ( errorRewriteLoop
    )
import Kore.Log.KoreLogOptions
    ( KoreLogOptions (..)
    )
import qualified Kore.ModelChecker.Bounded as Bounded
import Kore.Profiler.Data
    ( MonadProfiler
    )
import qualified Kore.Profiler.Profile as Profiler
    ( initialization
    )
import qualified Kore.Repl as Repl
import qualified Kore.Repl.Data as Repl.Data
import Kore.Rewriting.RewritingVariable
import Kore.Step
import Kore.Step.Rule
    ( extractImplicationClaims
    , extractRewriteAxioms
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
import Kore.Step.RulePattern
    ( ImplicationRule (..)
    , ReachabilityRule (..)
    , RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    , ToRulePattern (..)
    , getRewriteRule
    , lhsEqualsRhs
    )
import Kore.Step.RulePattern as RulePattern
    ( RulePattern (..)
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
    ( MonadSimplify
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Step.Transition
    ( runTransitionT
    )
import qualified Kore.Strategies.Goal as Goal
import Kore.Strategies.Verification
    ( AllClaims (AllClaims)
    , AlreadyProven (AlreadyProven)
    , Axioms (Axioms)
    , Stuck (..)
    , ToProve (ToProve)
    , verify
    )
import Kore.Syntax.Module
    ( ModuleName
    )
import Kore.Unparser
    ( unparseToText
    , unparseToText2
    )
import Log
    ( MonadLog
    )
import qualified Log
import qualified Logic
import SMT
    ( MonadSMT
    , SMT
    )

-- | Semantic rule used during execution.
type Rewrite = RewriteRule VariableName

-- | Function rule used during execution.
type Equality = Equation VariableName

-- | A collection of rules and simplifiers used during execution.
newtype Initialized = Initialized { rewriteRules :: [Rewrite] }

-- | Symbolic execution
exec
    ::  ( MonadIO smt
        , MonadLog smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadThrow smt
        )
    => Limit Natural
    -> VerifiedModule StepperAttributes
    -- ^ The main module
    -> ([RewriteRule RewritingVariableName] -> [Strategy (Prim (RewriteRule RewritingVariableName))])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike VariableName
    -- ^ The input pattern
    -> smt (TermLike VariableName)
exec breadthLimit verifiedModule strategy initialTerm =
    evalSimplifier verifiedModule' $ do
        initialized <- initialize verifiedModule
        let Initialized { rewriteRules } = initialized
            rewriteRules' = mkRewritingRule <$> rewriteRules
        finalConfig <-
            getFinalConfigOf $ do
                initialConfig <-
                    Pattern.simplify SideCondition.top
                        (Pattern.fromTermLike initialTerm)
                    >>= Logic.scatter
                let
                    updateQueue = \as ->
                        Strategy.unfoldDepthFirst as
                        >=> lift . Strategy.applyBreadthLimit breadthLimit
                    transit instr config =
                        Strategy.transitionRule transitionRule instr config
                        & runTransitionT
                        & fmap (map fst)
                        & lift
                Strategy.leavesM
                    updateQueue
                    (Strategy.unfoldTransition transit)
                    (strategy rewriteRules', initialConfig)
        let finalTerm = forceSort initialSort $ Pattern.toTermLike finalConfig
        return finalTerm
  where
    -- Get the first final configuration of an execution graph.
    getFinalConfigOf act =
        Logic.runLogicT act takeFirstResult elseBottom
      where
        takeFirstResult (_, config) _ = pure config
        elseBottom = pure (Pattern.bottomOf initialSort)
    verifiedModule' =
        IndexedModule.mapPatterns
            -- TODO (thomas.tuegel): Move this into Kore.Builtin
            (Builtin.internalize metadataTools)
            verifiedModule
    -- It's safe to build the MetadataTools using the external IndexedModule
    -- because MetadataTools doesn't retain any knowledge of the patterns which
    -- are internalized.
    metadataTools = MetadataTools.build verifiedModule
    initialSort = termLikeSort initialTerm

-- | Project the value of the exit cell, if it is present.
execGetExitCode
    ::  ( MonadIO smt
        , MonadLog smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadThrow smt
        )
    => VerifiedModule StepperAttributes
    -- ^ The main module
    -> ([RewriteRule RewritingVariableName] -> [Strategy (Prim (RewriteRule RewritingVariableName))])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike VariableName
    -- ^ The final pattern (top cell) to extract the exit code
    -> smt ExitCode
execGetExitCode indexedModule strategy' finalTerm =
    case resolveInternalSymbol indexedModule $ noLocationId "LblgetExitCode" of
        Nothing -> return ExitSuccess
        Just mkExitCodeSymbol -> do
            exitCodePattern <-
                -- TODO (thomas.tuegel): Run in original execution context.
                exec (Limit 1) indexedModule strategy'
                $ mkApplySymbol (mkExitCodeSymbol []) [finalTerm]
            case exitCodePattern of
                Builtin_ (Domain.BuiltinInt (Domain.InternalInt _ exit))
                  | exit == 0 -> return ExitSuccess
                  | otherwise -> return $ ExitFailure $ fromInteger exit
                _ -> return $ ExitFailure 111

-- | Symbolic search
search
    ::  ( MonadIO smt
        , MonadLog smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadThrow smt
        )
    => Limit Natural
    -> VerifiedModule StepperAttributes
    -- ^ The main module
    -> ([RewriteRule RewritingVariableName] -> [Strategy (Prim (RewriteRule RewritingVariableName))])
    -- ^ The strategy to use for execution; see examples in "Kore.Step.Step"
    -> TermLike VariableName
    -- ^ The input pattern
    -> Pattern VariableName
    -- ^ The pattern to match during execution
    -> Search.Config
    -- ^ The bound on the number of search matches and the search type
    -> smt (TermLike VariableName)
search breadthLimit verifiedModule strategy termLike searchPattern searchConfig
  =
    evalSimplifier verifiedModule $ do
        initialized <- initialize verifiedModule
        let Initialized { rewriteRules } = initialized
            rewriteRules' = mkRewritingRule <$> rewriteRules
        simplifiedPatterns <-
            Pattern.simplify SideCondition.top
            $ Pattern.fromTermLike termLike
        let
            initialPattern =
                case MultiOr.extractPatterns simplifiedPatterns of
                    [] -> Pattern.bottomOf (termLikeSort termLike)
                    (config : _) -> config
            runStrategy' =
                runStrategy breadthLimit transitionRule (strategy rewriteRules')
        executionGraph <- runStrategy' initialPattern
        let
            match target config = Search.matchWith target config
        solutionsLists <-
            searchGraph
                searchConfig
                (match SideCondition.topTODO searchPattern)
                executionGraph
        let
            solutions = concatMap MultiOr.extractPatterns solutionsLists
            orPredicate =
                makeMultipleOrPredicate (Condition.toPredicate <$> solutions)
        return (forceSort patternSort $ unwrapPredicate orPredicate)
  where
    patternSort = termLikeSort termLike


-- | Proving a spec given as a module containing rules to be proven
prove
    ::  forall smt
      . ( Log.WithLog Log.LogMessage smt
        , MonadCatch smt
        , MonadProfiler smt
        , MonadIO smt
        , MonadSMT smt
        )
    => Strategy.GraphSearchOrder
    -> Limit Natural
    -> Limit Natural
    -> VerifiedModule StepperAttributes
    -- ^ The main module
    -> VerifiedModule StepperAttributes
    -- ^ The spec module
    -> Maybe (VerifiedModule StepperAttributes)
    -- ^ The module containing the claims that were proven in a previous run.
    -> smt (Either Stuck ())
prove
    searchOrder
    breadthLimit
    depthLimit
    definitionModule
    specModule
    trustedModule
  =
    evalSimplifier definitionModule $ do
        initialized <-
            initializeProver
                definitionModule
                specModule
                trustedModule
        let InitializedProver { axioms, claims, alreadyProven } = initialized
        verify
            breadthLimit
            searchOrder
            (AllClaims claims)
            (Axioms axioms)
            (AlreadyProven (map unparseToText2 alreadyProven))
            (ToProve
                (map (\x -> (x,depthLimit))
                    (extractUntrustedClaims' claims)
                )
            )
            & runExceptT
  where
    extractUntrustedClaims' :: [ReachabilityRule] -> [ReachabilityRule]
    extractUntrustedClaims' = filter (not . Goal.isTrusted)

-- | Initialize and run the repl with the main and spec modules. This will loop
-- the repl until the user exits.
proveWithRepl
    :: VerifiedModule StepperAttributes
    -- ^ The main module
    -> VerifiedModule StepperAttributes
    -- ^ The spec module
    -> Maybe (VerifiedModule StepperAttributes)
    -- ^ The module containing the claims that were proven in a previous run.
    -> MVar (Log.LogAction IO Log.ActualEntry)
    -> Repl.Data.ReplScript
    -- ^ Optional script
    -> Repl.Data.ReplMode
    -- ^ Run in a specific repl mode
    -> Repl.Data.ScriptModeOutput
    -- ^ Optional flag for output in run-mode
    -> Repl.Data.OutputFile
    -- ^ Optional Output file
    -> ModuleName
    -> KoreLogOptions
    -> SMT ()
proveWithRepl
    definitionModule
    specModule
    trustedModule
    mvar
    replScript
    replMode
    scriptModeOutput
    outputFile
    mainModuleName
    logOptions
  =
    evalSimplifier definitionModule $ do
        initialized <-
            initializeProver
                definitionModule
                specModule
                trustedModule
        let InitializedProver { axioms, claims } = initialized
        Repl.runRepl
            axioms
            claims
            mvar
            replScript
            replMode
            scriptModeOutput
            outputFile
            mainModuleName
            logOptions

-- | Bounded model check a spec given as a module containing rules to be checked
boundedModelCheck
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadIO smt
        , MonadThrow smt
        )
    => Limit Natural
    -> Limit Natural
    -> VerifiedModule StepperAttributes
    -- ^ The main module
    -> VerifiedModule StepperAttributes
    -- ^ The spec module
    -> Strategy.GraphSearchOrder
    -> smt (Bounded.CheckResult (TermLike VariableName))
boundedModelCheck breadthLimit depthLimit definitionModule specModule searchOrder =
    evalSimplifier definitionModule $ do
        initialized <- initialize definitionModule
        let Initialized { rewriteRules } = initialized
            specClaims = extractImplicationClaims specModule
        assertSomeClaims specClaims
        assertSingleClaim specClaims
        let axioms = fmap Bounded.Axiom rewriteRules
            claims = fmap makeImplicationRule specClaims

        Bounded.checkClaim
            breadthLimit
            (Bounded.bmcStrategy axioms)
            searchOrder
            (head claims, depthLimit)

-- | Rule merging
mergeAllRules
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadIO smt
        )
    => VerifiedModule StepperAttributes
    -- ^ The main module
    -> [Text]
    -- ^ The list of rules to merge
    -> smt (Either Text [RewriteRule VariableName])
mergeAllRules = mergeRules Rules.mergeRules

-- | Rule merging
mergeRulesConsecutiveBatches
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadIO smt
        )
    => Int
    -- ^ Batch size
    -> VerifiedModule StepperAttributes
    -- ^ The main module
    -> [Text]
    -- ^ The list of rules to merge
    -> smt (Either Text [RewriteRule VariableName])
mergeRulesConsecutiveBatches batchSize =
    mergeRules (Rules.mergeRulesConsecutiveBatches batchSize)

-- | Rule merging in batches
mergeRules
    ::  ( Log.WithLog Log.LogMessage smt
        , MonadProfiler smt
        , MonadSMT smt
        , MonadIO smt
        )
    =>  (  NonEmpty (RewriteRule VariableName)
        -> Simplifier.SimplifierT smt [RewriteRule VariableName]
        )
    -- ^ The rule merger
    -> VerifiedModule StepperAttributes
    -- ^ The main module
    -> [Text]
    -- ^ The list of rules to merge
    -> smt (Either Text [RewriteRule VariableName])
mergeRules ruleMerger verifiedModule ruleNames =
    evalSimplifier verifiedModule $ do
        initialized <- initialize verifiedModule
        let Initialized { rewriteRules } = initialized

        let nonEmptyRules :: Either Text (NonEmpty (RewriteRule VariableName))
            nonEmptyRules = do
                rules <- extractRules rewriteRules ruleNames
                case rules of
                    [] -> Left "Empty rule list."
                    (r : rs) -> Right (r :| rs)

        case nonEmptyRules of
            (Left left) -> return (Left left)
            (Right rules) -> Right <$> ruleMerger rules

extractRules
    :: [RewriteRule VariableName]
    -> [Text]
    -> Either Text [RewriteRule VariableName]
extractRules rules = foldr addExtractRule (Right [])
  where
    addExtractRule
        :: Text
        -> Either Text [RewriteRule VariableName]
        -> Either Text [RewriteRule VariableName]
    addExtractRule ruleName processedRules =
        (:) <$> extractRule ruleName <*> processedRules

    maybeRuleUniqueId :: RewriteRule VariableName -> Maybe Text
    maybeRuleUniqueId
        (RewriteRule RulePattern
            { attributes = Attribute.Axiom
                { uniqueId = Attribute.UniqueId maybeName }
            }
        )
      =
        maybeName

    maybeRuleLabel :: RewriteRule VariableName -> Maybe Text
    maybeRuleLabel
        (RewriteRule RulePattern
            { attributes = Attribute.Axiom
                { label = Attribute.Label maybeName }
            }
        )
      =
        maybeName

    idRules :: [RewriteRule VariableName] -> [(Text, RewriteRule VariableName)]
    idRules = mapMaybe namedRule
      where
        namedRule rule = do
            name <- maybeRuleUniqueId rule
            return (name, rule)

    labelRules :: [RewriteRule VariableName] -> [(Text, RewriteRule VariableName)]
    labelRules = mapMaybe namedRule
      where
        namedRule rule = do
            name <- maybeRuleLabel rule
            return (name, rule)

    rulesByName :: Map.Map Text (RewriteRule VariableName)
    rulesByName = Map.union
        (Map.fromListWith
            (const $ const $ error "duplicate rule")
            (idRules rules)
        )
        (Map.fromListWith
            (const $ const $ error "duplicate rule")
            (labelRules rules)
        )

    extractRule :: Text -> Either Text (RewriteRule VariableName)
    extractRule ruleName =
        note
            ("Rule not found: '" <> ruleName <> "'.")
            (Map.lookup ruleName rulesByName)

assertSingleClaim :: Monad m => [claim] -> m ()
assertSingleClaim claims =
    when (length claims > 1) . error
        $ "More than one claim is found in the module."

assertSomeClaims :: Monad m => [claim] -> m ()
assertSomeClaims claims =
    when (null claims) . error
        $   "Unexpected empty set of claims.\n"
        ++  "Possible explanation: the frontend and the backend don't agree "
        ++  "on the representation of claims."

makeImplicationRule
    :: (Attribute.Axiom Symbol VariableName, ImplicationRule VariableName)
    -> ImplicationRule VariableName
makeImplicationRule (attributes, ImplicationRule rulePattern) =
    ImplicationRule rulePattern { attributes }

simplifyReachabilityRule
    :: MonadSimplify simplifier
    => ReachabilityRule
    -> simplifier ReachabilityRule
simplifyReachabilityRule rule = do
    rule' <- Rule.simplifyRewriteRule (RewriteRule . toRulePattern $ rule)
    return (Goal.fromRulePattern rule . getRewriteRule $ rule')

-- | Collect various rules and simplifiers in preparation to execute.
initialize
    :: forall simplifier
    .  MonadSimplify simplifier
    => VerifiedModule StepperAttributes
    -> simplifier Initialized
initialize verifiedModule = do
    let rewriteRules = extractRewriteAxioms verifiedModule
        simplifyToList
            :: SimplifyRuleLHS rule
            => rule
            -> simplifier [rule]
        simplifyToList rule = do
            simplified <- simplifyRuleLhs rule
            return (MultiAnd.extractPatterns simplified)
    traverse_
        errorRewriteLoop
        $ find (lhsEqualsRhs . getRewriteRule) rewriteRules
    rewriteAxioms <- Profiler.initialization "simplifyRewriteRule" $
        mapM simplifyToList rewriteRules
    pure Initialized { rewriteRules = concat rewriteAxioms }

data InitializedProver =
    InitializedProver
        { axioms :: ![Goal.Rule ReachabilityRule]
        , claims :: ![ReachabilityRule]
        , alreadyProven :: ![ReachabilityRule]
        }

data MaybeChanged a = Changed !a | Unchanged !a

fromMaybeChanged :: MaybeChanged a -> a
fromMaybeChanged (Changed a) = a
fromMaybeChanged (Unchanged a) = a

-- | Collect various rules and simplifiers in preparation to execute.
initializeProver
    :: forall simplifier
    .  MonadSimplify simplifier
    => VerifiedModule StepperAttributes
    -> VerifiedModule StepperAttributes
    -> Maybe (VerifiedModule StepperAttributes)
    -> simplifier InitializedProver
initializeProver definitionModule specModule maybeTrustedModule = do
    initialized <- initialize definitionModule
    tools <- Simplifier.askMetadataTools
    let Initialized { rewriteRules } = initialized
        changedSpecClaims :: [MaybeChanged ReachabilityRule]
        changedSpecClaims =
            expandClaim tools <$> Goal.extractClaims specModule
        simplifyToList
            :: SimplifyRuleLHS rule
            => rule
            -> simplifier [rule]
        simplifyToList rule = do
            simplified <- simplifyRuleLhs rule
            return (MultiAnd.extractPatterns simplified)

        trustedClaims :: [ReachabilityRule]
        trustedClaims =
            fmap Goal.extractClaims maybeTrustedModule & fromMaybe []

    mapM_ logChangedClaim changedSpecClaims

    let specClaims :: [ReachabilityRule]
        specClaims = map fromMaybeChanged changedSpecClaims
    -- This assertion should come before simplifying the claims,
    -- since simplification should remove all trivial claims.
    assertSomeClaims specClaims
    simplifiedSpecClaims <- mapM simplifyToList specClaims
    claims <- Profiler.initialization "simplifyRuleOnSecond"
        $ traverse simplifyReachabilityRule (concat simplifiedSpecClaims)
    let axioms = coerce . mkRewritingRule <$> rewriteRules
        alreadyProven = trustedClaims
    pure InitializedProver { axioms, claims, alreadyProven }
  where
    expandClaim
        :: SmtMetadataTools attributes
        -> ReachabilityRule
        -> MaybeChanged ReachabilityRule
    expandClaim tools claim =
        if claim /= expanded
            then Changed expanded
            else Unchanged claim
      where
        expanded = expandSingleConstructors tools claim

    logChangedClaim
        :: MaybeChanged ReachabilityRule
        -> simplifier ()
    logChangedClaim (Changed claim) =
        Log.logInfo ("Claim variables were expanded:\n" <> unparseToText claim)
    logChangedClaim (Unchanged _) = return ()
