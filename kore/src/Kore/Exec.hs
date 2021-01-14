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
import Control.DeepSeq
    ( deepseq
    )
import qualified Control.Lens as Lens
import Control.Monad
    ( (>=>)
    )
import Control.Monad.Catch
    ( MonadMask
    )
import Control.Monad.Trans.Except
    ( ExceptT
    , runExceptT
    , throwE
    )
import Data.Coerce
    ( coerce
    )
import Data.Generics.Product
    ( field
    )
import Data.Generics.Wrapped
    ( _Unwrapped
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
import Kore.Internal.InternalInt
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrPattern as OrPattern
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
import Kore.Log.ErrorRuleMergeDuplicate
    ( errorRuleMergeDuplicateIds
    , errorRuleMergeDuplicateLabels
    )
import Kore.Log.InfoExecDepth
import Kore.Log.KoreLogOptions
    ( KoreLogOptions (..)
    )
import Kore.Log.WarnTrivialClaim
import qualified Kore.ModelChecker.Bounded as Bounded
import Kore.Reachability
    ( AllClaims (AllClaims)
    , AlreadyProven (AlreadyProven)
    , Axioms (Axioms)
    , ProveClaimsResult (..)
    , Rule (ReachabilityRewriteRule)
    , SomeClaim (..)
    , ToProve (ToProve)
    , extractClaims
    , isTrusted
    , lensClaimPattern
    , proveClaims
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
    , RewriteRule (RewriteRule)
    , getRewriteRule
    , lhsEqualsRhs
    , mkRewritingRule
    , unRewritingRule
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
    , scatter
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
import Logic
    ( LogicT
    , observeAllT
    )
import qualified Logic
import Prof
import SMT
    ( MonadSMT
    , SMT
    )

-- | Semantic rule used during execution.
type Rewrite = RewriteRule RewritingVariableName

-- | Function rule used during execution.
type Equality = Equation VariableName

-- | A collection of rules and simplifiers used during execution.
newtype Initialized = Initialized { rewriteRules :: [Rewrite] }

-- | Symbolic execution
exec
    :: forall smt
    .   ( MonadIO smt
        , MonadLog smt
        , MonadSMT smt
        , MonadMask smt
        , MonadProf smt
        )
    => Limit Natural
    -> Limit Natural
    -> VerifiedModule StepperAttributes
    -- ^ The main module
    -> ExecutionMode
    -> TermLike VariableName
    -- ^ The input pattern
    -> smt (ExitCode, TermLike VariableName)
exec depthLimit breadthLimit verifiedModule strategy initialTerm =
    evalSimplifier verifiedModule' $ do
        initialized <- initializeAndSimplify verifiedModule
        let Initialized { rewriteRules } = initialized
        finals <-
            getFinalConfigsOf $ do
                initialConfig <-
                    Pattern.simplify SideCondition.top
                        (Pattern.fromTermLike initialTerm)
                    >>= Logic.scatter
                let
                    updateQueue = \as ->
                        Strategy.unfoldDepthFirst as
                        >=> lift
                            . Strategy.applyBreadthLimit
                                breadthLimit
                                dropStrategy
                    rewriteGroups = groupRewritesByPriority rewriteRules
                    transit instr config =
                        Strategy.transitionRule
                            (transitionRule rewriteGroups strategy
                                & profTransitionRule
                                & trackExecDepth)
                            instr
                            config
                        & runTransitionT
                        & fmap (map fst)
                        & lift
                Strategy.leavesM
                    updateQueue
                    (Strategy.unfoldTransition transit)
                    ( limitedExecutionStrategy depthLimit
                    , (ExecDepth 0, Start (mkRewritingPattern initialConfig))
                    )
        let (depths, finalConfigs) = unzip finals
        infoExecDepth (maximum depths)
        let finalConfigs' =
                MultiOr.make
                $ getRewritingPattern
                . extractProgramState
                <$> finalConfigs
        exitCode <- getExitCode verifiedModule finalConfigs'
        let finalTerm = forceSort initialSort $ OrPattern.toTermLike finalConfigs'
        return (exitCode, finalTerm)
  where
    dropStrategy = snd
    getFinalConfigsOf act = observeAllT $ fmap snd act
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

{- | Modify a 'TransitionRule' to track the depth of the execution graph.
 -}
trackExecDepth
    :: TransitionRule monad rule state
    -> TransitionRule monad rule (ExecDepth, state)
trackExecDepth transit prim (execDepth, execState) = do
    execState' <- transit prim execState
    let execDepth' = (if didRewrite execState' then succ else id) execDepth
    pure (execDepth', execState')
  where
    didRewrite _ = isRewrite prim

    isRewrite Rewrite = True
    isRewrite _ = False

{- | Add profiling markers to a 'TransitionRule'.
-}
profTransitionRule
    :: forall monad rule state
    .  MonadProf monad
    => TransitionRule monad rule state
    -> TransitionRule monad rule state
profTransitionRule rule prim proofState =
    case prim of
        Rewrite -> Just ":rewrite:"
        Simplify -> Just ":simplify:"
        Begin -> Nothing
    & \case
        Just marker -> lift (traceProf marker (runTransitionT go)) >>= scatter
        Nothing -> go
  where
    go = rule prim proofState

-- | Project the value of the exit cell, if it is present.
getExitCode
    :: forall simplifier
    .  (MonadIO simplifier, MonadSimplify simplifier)
    => VerifiedModule StepperAttributes
    -- ^ The main module
    -> OrPattern.OrPattern VariableName
    -- ^ The final configuration(s) of execution
    -> simplifier ExitCode
getExitCode indexedModule configs =
    takeExitCode $ \mkExitCodeSymbol -> do
        let mkGetExitCode t = mkApplySymbol (mkExitCodeSymbol []) [t]
        exitCodePatterns <-
            do
                config <- Logic.scatter configs
                Pattern.simplifyTopConfiguration (mkGetExitCode <$> config)
                    >>= Logic.scatter
            & MultiOr.observeAllT
        let exitCode =
                case toList (MultiOr.map Pattern.term exitCodePatterns) of
                    [exitTerm] -> extractExit exitTerm
                    _      -> ExitFailure 111
        return exitCode
  where
    extractExit = \case
        InternalInt_ InternalInt { internalIntValue = exit }
          | exit == 0 -> ExitSuccess
          | otherwise -> ExitFailure (fromInteger exit)
        _ -> ExitFailure 111

    resolve = resolveInternalSymbol indexedModule . noLocationId

    takeExitCode
        :: (([Sort] -> Symbol) -> simplifier ExitCode)
        -> simplifier ExitCode
    takeExitCode act =
        resolve "LblgetExitCode"
        & maybe (pure ExitSuccess) act

-- | Symbolic search
search
    ::  ( MonadIO smt
        , MonadLog smt
        , MonadSMT smt
        , MonadMask smt
        , MonadProf smt
        )
    => Limit Natural
    -> Limit Natural
    -> VerifiedModule StepperAttributes
    -- ^ The main module
    -> TermLike VariableName
    -- ^ The input pattern
    -> Pattern VariableName
    -- ^ The pattern to match during execution
    -> Search.Config
    -- ^ The bound on the number of search matches and the search type
    -> smt (TermLike VariableName)
search depthLimit breadthLimit verifiedModule termLike searchPattern searchConfig
  =
    evalSimplifier verifiedModule $ do
        initialized <- initializeAndSimplify verifiedModule
        let Initialized { rewriteRules } = initialized
        simplifiedPatterns <-
            Pattern.simplify SideCondition.top
            $ Pattern.fromTermLike termLike
        let
            initialPattern =
                case toList simplifiedPatterns of
                    [] -> Pattern.bottomOf (termLikeSort termLike)
                    (config : _) -> config
            rewriteGroups =
                groupRewritesByPriority rewriteRules
            runStrategy' =
                runStrategy
                    breadthLimit
                    -- search relies on exploring
                    -- the entire space of states.
                    (transitionRule rewriteGroups All
                        & profTransitionRule)
                    (limitedExecutionStrategy depthLimit)
        executionGraph <-
            runStrategy' (Start $ mkRewritingPattern initialPattern)
        let
            match target config1 config2 =
                Search.matchWith
                    target
                    config1
                    (extractProgramState config2)
        solutionsLists <-
            searchGraph
                searchConfig
                (match
                    SideCondition.topTODO
                    (mkRewritingPattern searchPattern)
                )
                executionGraph
        let
            solutions = concatMap toList solutionsLists
            orPredicate =
                makeMultipleOrPredicate (Condition.toPredicate <$> solutions)
        return
            . forceSort patternSort
            . getRewritingTerm
            . unwrapPredicate
            $ orPredicate
  where
    patternSort = termLikeSort termLike

-- | Proving a spec given as a module containing rules to be proven
prove
    ::  forall smt
      . ( MonadLog smt
        , MonadMask smt
        , MonadIO smt
        , MonadSMT smt
        , MonadProf smt
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
    -> smt ProveClaimsResult
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
        proveClaims
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
  where
    extractUntrustedClaims' :: [SomeClaim] -> [SomeClaim]
    extractUntrustedClaims' = filter (not . isTrusted)

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
    ::  ( MonadLog smt
        , MonadSMT smt
        , MonadIO smt
        , MonadMask smt
        , MonadProf smt
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
        initialized <- initializeAndSimplify definitionModule
        let Initialized { rewriteRules } = initialized
            specClaims = extractImplicationClaims specModule
        assertSomeClaims specClaims
        assertSingleClaim specClaims
        let axioms = fmap (Bounded.Axiom . unRewritingRule) rewriteRules
            claims = fmap makeImplicationRule specClaims

        Bounded.checkClaim
            breadthLimit
            (Bounded.bmcStrategy axioms)
            searchOrder
            (head claims, depthLimit)

-- | Rule merging
mergeAllRules
    ::  ( MonadLog smt
        , MonadSMT smt
        , MonadIO smt
        , MonadProf smt
        , MonadMask smt
        )
    => VerifiedModule StepperAttributes
    -- ^ The main module
    -> [Text]
    -- ^ The list of rules to merge
    -> smt (Either Text [RewriteRule VariableName])
mergeAllRules = mergeRules Rules.mergeRules

-- | Rule merging
mergeRulesConsecutiveBatches
    ::  ( MonadLog smt
        , MonadSMT smt
        , MonadIO smt
        , MonadProf smt
        , MonadMask smt
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
    ::  ( MonadLog smt
        , MonadSMT smt
        , MonadIO smt
        , MonadProf smt
        , MonadMask smt
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
    evalSimplifier verifiedModule $ runExceptT $ do
        initialized <- initializeWithoutSimplification verifiedModule
        let Initialized { rewriteRules } = initialized
            rewriteRules' = unRewritingRule <$> rewriteRules
        rules <- extractAndSimplifyRules rewriteRules' ruleNames
        lift $ ruleMerger rules

extractAndSimplifyRules
    :: forall m
    .  MonadSimplify m
    => [RewriteRule VariableName]
    -> [Text]
    -> ExceptT Text m (NonEmpty (RewriteRule VariableName))
extractAndSimplifyRules rules names = do
    let rulesById = mapMaybe ruleById rules
        rulesByLabel = mapMaybe ruleByLabel rules
    whenDuplicate errorRuleMergeDuplicateIds rulesById
    whenDuplicate errorRuleMergeDuplicateLabels rulesByLabel
    let ruleRegistry = Map.fromList (rulesById <> rulesByLabel)
    extractedRules <-
        traverse (extractRule ruleRegistry >=> simplifyRuleLhs) names
        & fmap (>>= toList)
    case extractedRules of
        [] -> throwE "Empty rule list."
        (r : rs) -> return (r :| rs)

  where
    ruleById = ruleByName (field @"uniqueId")

    ruleByLabel = ruleByName (field @"label")

    ruleByName lens rule = do
        name <-
            Lens.view
                (_Unwrapped . field @"attributes" . lens . _Unwrapped)
                rule
        return (name, rule)

    extractRule registry ruleName =
        maybe
            (throwE $ "Rule not found: '" <> ruleName <> "'.")
            return
            (Map.lookup ruleName registry)

    whenDuplicate logError withNames = do
        let duplicateNames =
                findCollisions . mkMapWithCollisions $ withNames
        unless (null duplicateNames) (logError duplicateNames)

mkMapWithCollisions
    :: Ord key
    => [(key, val)]
    -> Map.Map key [val]
mkMapWithCollisions pairs =
    Map.fromListWith (<>)
    $ (fmap . fmap) pure pairs

findCollisions :: Map.Map key [val] -> Map.Map key [val]
findCollisions = filter (not . isSingleton)
  where
    isSingleton [_] = True
    isSingleton _ = False

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

simplifySomeClaim
    :: MonadSimplify simplifier
    => SomeClaim
    -> simplifier SomeClaim
simplifySomeClaim rule = do
    let claim = Lens.view lensClaimPattern rule
    claim' <- Rule.simplifyClaimPattern claim
    return $ Lens.set lensClaimPattern claim' rule

initializeAndSimplify
    :: MonadSimplify simplifier
    => VerifiedModule StepperAttributes
    -> simplifier Initialized
initializeAndSimplify verifiedModule =
    initialize (simplifyRuleLhs >=> Logic.scatter) verifiedModule

initializeWithoutSimplification
    :: MonadSimplify simplifier
    => VerifiedModule StepperAttributes
    -> simplifier Initialized
initializeWithoutSimplification verifiedModule =
    initialize return verifiedModule

-- | Collect various rules and simplifiers in preparation to execute.
initialize
    :: forall simplifier
    .  MonadSimplify simplifier
    => (RewriteRule VariableName -> LogicT simplifier (RewriteRule VariableName))
    -> VerifiedModule StepperAttributes
    -> simplifier Initialized
initialize simplificationProcedure verifiedModule = do
    rewriteRules <-
        Logic.observeAllT $ do
            rule <- Logic.scatter (extractRewriteAxioms verifiedModule)
            initializeRule rule
    pure Initialized { rewriteRules }
  where
    initializeRule
        :: RewriteRule VariableName
        -> LogicT simplifier (RewriteRule RewritingVariableName)
    initializeRule rule = do
        simplRule <- simplificationProcedure rule
        when (lhsEqualsRhs $ getRewriteRule simplRule)
            (errorRewriteLoop simplRule)
        let renamedRule = mkRewritingRule simplRule
        deepseq renamedRule pure renamedRule

data InitializedProver =
    InitializedProver
        { axioms :: ![Rule SomeClaim]
        , claims :: ![SomeClaim]
        , alreadyProven :: ![SomeClaim]
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
    initialized <- initializeAndSimplify definitionModule
    tools <- Simplifier.askMetadataTools
    let Initialized { rewriteRules } = initialized
        changedSpecClaims :: [MaybeChanged SomeClaim]
        changedSpecClaims = expandClaim tools <$> extractClaims specModule
        simplifyToList :: SomeClaim -> simplifier [SomeClaim]
        simplifyToList rule = do
            simplified <- simplifyRuleLhs rule
            let result = toList simplified
            when (null result) $ warnTrivialClaimRemoved rule
            return result

        trustedClaims :: [SomeClaim]
        trustedClaims = fmap extractClaims maybeTrustedModule & fromMaybe []

    mapM_ logChangedClaim changedSpecClaims

    let specClaims :: [SomeClaim]
        specClaims = map fromMaybeChanged changedSpecClaims
    -- This assertion should come before simplifying the claims,
    -- since simplification should remove all trivial claims.
    assertSomeClaims specClaims
    simplifiedSpecClaims <- mapM simplifyToList specClaims
    claims <- traverse simplifySomeClaim (concat simplifiedSpecClaims)
    let axioms = coerce <$> rewriteRules
        alreadyProven = trustedClaims
    pure InitializedProver { axioms, claims, alreadyProven }
  where
    expandClaim
        :: SmtMetadataTools attributes
        -> SomeClaim
        -> MaybeChanged SomeClaim
    expandClaim tools claim =
        if claim /= expanded
            then Changed expanded
            else Unchanged claim
      where
        expanded = expandSingleConstructors tools claim

    logChangedClaim
        :: MaybeChanged SomeClaim
        -> simplifier ()
    logChangedClaim (Changed claim) =
        Log.logInfo ("Claim variables were expanded:\n" <> unparseToText claim)
    logChangedClaim (Unchanged _) = return ()
