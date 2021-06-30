{- |
Module      : Kore.Interpreter
Description : REPL interpreter
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}
module Kore.Repl.Interpreter (
    replInterpreter,
    replInterpreter0,
    showUsageMessage,
    showStepStoppedMessage,
    showProofStatus,
    showClaimSwitch,
    printIfNotEmpty,
    showRewriteRule,
    parseEvalScript,
    showAliasError,
    saveSessionWithMessage,
    formatUnificationMessage,
    allProofs,
    ReplStatus (..),
    showCurrentClaimIndex,
) where

import Control.Lens (
    (%=),
    (.=),
 )
import qualified Control.Lens as Lens
import Control.Monad (
    (<=<),
 )
import Control.Monad.Extra (
    ifM,
    loop,
    loopM,
 )
import Control.Monad.RWS.Strict (
    MonadWriter,
    RWST,
    ask,
    runRWST,
    tell,
 )
import Control.Monad.Reader (
    MonadReader,
    ReaderT (..),
 )
import qualified Control.Monad.Reader as Reader (
    ask,
 )
import Control.Monad.State.Class (
    get,
    put,
 )
import Control.Monad.State.Strict (
    MonadState,
    StateT (..),
    execStateT,
 )
import qualified Control.Monad.Trans.Class as Monad.Trans
import Control.Monad.Trans.Except (
    runExceptT,
 )
import Data.Coerce (
    coerce,
 )
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.PatriciaTree (
    Gr,
 )
import qualified Data.Graph.Inductive.Query.BFS as Graph
import qualified Data.GraphViz as Graph
import qualified Data.GraphViz.Attributes.Complete as Graph.Attr
import Data.IORef (
    IORef,
    modifyIORef,
    newIORef,
    readIORef,
 )
import qualified Data.List as List
import Data.List.Extra (
    upper,
 )
import qualified Data.Map.Strict as Map
import Data.Maybe (
    fromJust,
 )
import Data.Sequence (
    Seq,
 )
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Typeable as Typeable
import GHC.Exts (
    toList,
 )
import GHC.IO.Handle (
    hGetContents,
    hPutStr,
 )
import GHC.Natural (
    naturalToInt,
 )
import Kore.Attribute.Axiom (
    SourceLocation (..),
 )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Label as AttrLabel
import Kore.Attribute.Pattern.FreeVariables (
    freeVariables,
 )
import Kore.Attribute.RuleIndex (
    RuleIndex (..),
 )
import Kore.Internal.Condition (
    Condition,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    fromConditionWithReplacements,
 )
import Kore.Internal.TermLike (
    TermLike,
 )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Log as Log
import Kore.Log.WarnIfLowProductivity (
    warnIfLowProductivity,
 )
import Kore.Reachability (
    ClaimState (..),
    ClaimStateTransformer (..),
    CommonClaimState,
    Rule (ReachabilityRewriteRule),
    SomeClaim (..),
    claimState,
    extractUnproven,
    getConfiguration,
    getDestination,
    isTrusted,
    makeTrusted,
 )
import qualified Kore.Reachability.ClaimState as ClaimState
import Kore.Repl.Data
import Kore.Repl.Parser
import Kore.Repl.State
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    getRewritingPattern,
 )
import qualified Kore.Rewrite.RulePattern as RulePattern
import qualified Kore.Rewrite.Strategy as Strategy
import Kore.Simplify.Data (
    MonadSimplify,
 )
import Kore.Syntax.Application
import qualified Kore.Syntax.Id as Id (
    Id (..),
 )
import Kore.Syntax.Variable
import Kore.Unparser (
    Unparse,
    unparse,
    unparseToString,
 )
import Numeric.Natural
import Prelude.Kore hiding (
    toList,
 )
import Pretty (
    Pretty (..),
 )
import qualified Pretty
import System.Directory (
    doesDirectoryExist,
    doesFileExist,
    findExecutable,
 )
import System.Exit
import System.FilePath (
    splitFileName,
    (<.>),
 )
import System.IO (
    IOMode (..),
    hPutStrLn,
    stderr,
    withFile,
 )
import System.Process (
    StdStream (CreatePipe),
    createProcess,
    proc,
    std_in,
    std_out,
 )
import Text.Megaparsec (
    ParseErrorBundle (..),
    ShowErrorComponent (..),
    errorBundlePretty,
    mapParseError,
    parseMaybe,
    runParser,
 )

{- | Warning: you should never use WriterT or RWST. It is used here with
 _great care_ of evaluating the RWST to a StateT immediately, and thus getting
 rid of the WriterT part of the stack. This happens in the implementation of
 'replInterpreter'.
-}
type ReplM m a = RWST (Config m) ReplOutput ReplState m a

data ReplStatus = Continue | SuccessStop | FailStop
    deriving stock (Eq, Show)

-- | Interprets a REPL command in a stateful Simplifier context.
replInterpreter ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    (String -> IO ()) ->
    ReplCommand ->
    ReaderT (Config m) (StateT ReplState m) ReplStatus
replInterpreter fn cmd =
    replInterpreter0
        (PrintAuxOutput fn)
        (PrintKoreOutput fn)
        cmd

replInterpreter0 ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    PrintAuxOutput ->
    PrintKoreOutput ->
    ReplCommand ->
    ReaderT (Config m) (StateT ReplState m) ReplStatus
replInterpreter0 printAux printKore replCmd = do
    let command = case replCmd of
            ShowUsage -> showUsage $> Continue
            Help -> help $> Continue
            ShowClaim mc -> showClaim mc $> Continue
            ShowAxiom ea -> showAxiom ea $> Continue
            Prove i -> prove i $> Continue
            ShowGraph v mfile out -> showGraph v mfile out $> Continue
            ProveSteps n -> proveSteps n $> Continue
            ProveStepsF n -> proveStepsF n $> Continue
            SelectNode i -> selectNode i $> Continue
            ShowConfig mc -> showConfig mc $> Continue
            ShowDest mc -> showDest mc $> Continue
            OmitCell c -> omitCell c $> Continue
            ShowLeafs -> showLeafs $> Continue
            ShowRule mc -> showRule mc $> Continue
            ShowRules ns -> showRules ns $> Continue
            ShowPrecBranch mn -> showPrecBranch mn $> Continue
            ShowChildren mn -> showChildren mn $> Continue
            Label ms -> label ms $> Continue
            LabelAdd l mn -> labelAdd l mn $> Continue
            LabelDel l -> labelDel l $> Continue
            Redirect inn file ->
                redirect inn file
                    $> Continue
            Try ref -> tryAxiomClaim ref $> Continue
            TryF ac -> tryFAxiomClaim ac $> Continue
            Clear n -> clear n $> Continue
            SaveSession file -> saveSession file $> Continue
            SavePartialProof mn f -> savePartialProof mn f $> Continue
            Pipe inn file args ->
                pipe inn file args
                    $> Continue
            AppendTo inn file ->
                appendTo inn file
                    $> Continue
            Alias a -> alias a $> Continue
            TryAlias name ->
                tryAlias name printAux printKore
            LoadScript file ->
                loadScript file
                    $> Continue
            ProofStatus -> proofStatus $> Continue
            Log opts -> log opts $> Continue
            DebugAttemptEquation op -> debugAttemptEquation op $> Continue
            DebugApplyEquation op -> debugApplyEquation op $> Continue
            DebugEquation op -> debugEquation op $> Continue
            Exit -> exit
    (ReplOutput output, shouldContinue) <- evaluateCommand command
    liftIO $
        traverse_
            ( replOut
                (unPrintAuxOutput printAux)
                (unPrintKoreOutput printKore)
            )
            output
    case shouldContinue of
        Continue -> pure Continue
        SuccessStop -> do
            warnProductivity
            liftIO exitSuccess
        FailStop -> do
            warnProductivity
            liftIO . exitWith $ ExitFailure 2
  where
    warnProductivity = do
        Config{kFileLocations} <- ask
        warnIfLowProductivity kFileLocations

    -- Extracts the Writer out of the RWST monad using the current state
    -- and updates the state, returning the writer output along with the
    -- monadic result.
    evaluateCommand ::
        ReplM m ReplStatus ->
        ReaderT (Config m) (StateT ReplState m) (ReplOutput, ReplStatus)
    evaluateCommand c = do
        st <- get
        config <- Reader.ask
        (ext, st', w) <-
            Monad.Trans.lift $
                Monad.Trans.lift $
                    runRWST c config st
        put st'
        pure (w, ext)

showUsageMessage :: String
showUsageMessage = "Could not parse command, try using 'help'."

showStepStoppedMessage :: Natural -> StepResult -> String
showStepStoppedMessage n sr =
    "Stopped after "
        <> show n
        <> " step(s) due to "
        <> case sr of
            NoResult ->
                "reaching end of proof on current branch."
            SingleResult _ -> ""
            BranchResult xs ->
                "branching on "
                    <> show (fmap unReplNode xs)

showUsage :: MonadWriter ReplOutput m => m ()
showUsage = putStrLn' showUsageMessage

exit ::
    MonadIO m =>
    ReplM m ReplStatus
exit = do
    proofs <- allProofs
    ofile <- Lens.view (field @"outputFile")
    newClaims <- generateInProgressClaims
    sort <- currentClaimSort
    let conj = conjOfClaims newClaims sort
        printTerm = maybe putStrLn writeFile (unOutputFile ofile)
    liftIO . printTerm . unparseToString $ conj
    if isCompleted (Map.elems proofs)
        then return SuccessStop
        else return FailStop
  where
    isCompleted :: [GraphProofStatus] -> Bool
    isCompleted = all (\x -> x == Completed || x == TrustedClaim)

help :: MonadWriter ReplOutput m => m ()
help = putStrLn' helpText

-- | Prints a claim using an index in the claims list.
showClaim ::
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    Maybe (Either ClaimIndex RuleName) ->
    m ()
showClaim =
    \case
        Nothing -> do
            currentClaimIndex <- Lens.use (field @"claimIndex")
            currentClaim <- Lens.use (field @"claim")
            putStrLn' . showCurrentClaimIndex $ currentClaimIndex
            tell . makeKoreReplOutput . unparseToString $ currentClaim
        Just indexOrName -> do
            claim <-
                either
                    (getClaimByIndex . unClaimIndex)
                    (getClaimByName . unRuleName)
                    indexOrName
            maybe printNotFound (tell . showRewriteRule) claim

-- | Prints an axiom using an index in the axioms list.
showAxiom ::
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    -- | index in the axioms list
    Either AxiomIndex RuleName ->
    m ()
showAxiom indexOrName = do
    axiom <-
        either
            (getAxiomByIndex . unAxiomIndex)
            (getAxiomByName . unRuleName)
            indexOrName
    maybe printNotFound (tell . showRewriteRule) axiom

-- | Changes the currently focused proof, using an index in the claims list.
prove ::
    forall m.
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    -- | index in the claims list
    Either ClaimIndex RuleName ->
    m ()
prove indexOrName = do
    claim' <-
        either
            (getClaimByIndex . unClaimIndex)
            (getClaimByName . unRuleName)
            indexOrName
    maybe
        printNotFound
        startProving
        claim'
  where
    startProving :: SomeClaim -> m ()
    startProving claim
        | isTrusted claim =
            putStrLn' $
                "Cannot switch to proving claim "
                    <> showIndexOrName indexOrName
                    <> ". Claim is trusted."
        | otherwise = do
            claimIndex <-
                either
                    (return . return)
                    (getClaimIndexByName . unRuleName)
                    indexOrName
            switchToProof claim $ fromJust claimIndex
            putStrLn' $
                "Switched to proving claim "
                    <> showIndexOrName indexOrName

showClaimSwitch :: Either ClaimIndex RuleName -> String
showClaimSwitch indexOrName =
    "Switched to proving claim "
        <> showIndexOrName indexOrName

showIndexOrName ::
    Either ClaimIndex RuleName ->
    String
showIndexOrName =
    either (show . unClaimIndex) (show . unRuleName)

showGraph ::
    MonadIO m =>
    MonadWriter ReplOutput m =>
    Maybe GraphView ->
    Maybe FilePath ->
    Maybe Graph.GraphvizOutput ->
    MonadState ReplState m =>
    m ()
showGraph view mfile out = do
    let format = fromMaybe Graph.Svg out
    graph <- getInnerGraph
    processedGraph <-
        case view of
            Just Expanded ->
                return $ Graph.emap Just graph
            _ ->
                maybe (showOriginalGraph graph) return (smoothOutGraph graph)
    installed <- liftIO Graph.isGraphvizInstalled
    if installed
        then
            liftIO $
                maybe
                    (showDotGraph processedGraph)
                    (saveDotGraph processedGraph format)
                    mfile
        else putStrLn' "Graphviz is not installed."
  where
    showOriginalGraph graph = do
        putStrLn'
            "Could not process execution graph for visualization.\
            \ Will default to showing the full graph."
        return $ Graph.emap Just graph

-- | Executes 'n' prove steps, or until branching occurs.
proveSteps ::
    MonadSimplify m =>
    MonadIO m =>
    -- | maximum number of steps to perform
    Natural ->
    ReplM m ()
proveSteps n = do
    let node = ReplNode . fromEnum $ n
    result <- loopM performStepNoBranching (n, SingleResult node)
    case result of
        (0, SingleResult _) -> pure ()
        (done, res) ->
            putStrLn' $ showStepStoppedMessage (n - done - 1) res

{- | Executes 'n' prove steps, distributing over branches. It will perform less
than 'n' steps if the proof is stuck or completed in less than 'n' steps.
-}
proveStepsF ::
    MonadSimplify m =>
    MonadIO m =>
    -- | maximum number of steps to perform
    Natural ->
    ReplM m ()
proveStepsF n = do
    node <- Lens.use (field @"node")
    recursiveForcedStep n node
    graph <- getInnerGraph
    let targetNode = getInterestingBranchingNode n graph node
    case targetNode of
        Nothing -> putStrLn' "Proof completed on all branches."
        Just someNode -> selectNode someNode

-- | Loads a script from a file.
loadScript ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    -- | path to file
    FilePath ->
    ReplM m ()
loadScript file = parseEvalScript file DisableOutput

-- | Change the general log settings.
log ::
    MonadState ReplState m =>
    GeneralLogOptions ->
    m ()
log generalLogOptions =
    field @"koreLogOptions" %= generalLogOptionsTransformer generalLogOptions

{- | Log debugging information about attempting to apply
 specific equations.
-}
debugAttemptEquation ::
    MonadState ReplState m =>
    Log.DebugAttemptEquationOptions ->
    m ()
debugAttemptEquation debugAttemptEquationOptions =
    field @"koreLogOptions"
        %= debugAttemptEquationTransformer debugAttemptEquationOptions

-- | Log when specific equations apply.
debugApplyEquation ::
    MonadState ReplState m =>
    Log.DebugApplyEquationOptions ->
    m ()
debugApplyEquation debugApplyEquationOptions =
    field @"koreLogOptions"
        %= debugApplyEquationTransformer debugApplyEquationOptions

{- | Log the attempts and the applications of specific
 equations.
-}
debugEquation ::
    MonadState ReplState m =>
    Log.DebugEquationOptions ->
    m ()
debugEquation debugEquationOptions =
    field @"koreLogOptions"
        %= debugEquationTransformer debugEquationOptions

-- | Focuses the node with id equals to 'n'.
selectNode ::
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    -- | node identifier
    ReplNode ->
    m ()
selectNode rnode = do
    graph <- getInnerGraph
    let i = unReplNode rnode
    if i `elem` Graph.nodes graph
        then field @"node" .= rnode
        else putStrLn' "Invalid node!"

-- | Shows configuration at node 'n', or current node if 'Nothing' is passed.
showConfig ::
    Monad m =>
    -- | 'Nothing' for current node, or @Just n@ for a specific node identifier
    Maybe ReplNode ->
    ReplM m ()
showConfig =
    showClaimStateComponent "Config" (from @_ @(OrPattern _) . getConfiguration)

-- | Shows destination at node 'n', or current node if 'Nothing' is passed.
showDest ::
    Monad m =>
    -- | 'Nothing' for current node, or @Just n@ for a specific node identifier
    Maybe ReplNode ->
    ReplM m ()
showDest =
    showClaimStateComponent
        "Destination"
        getDestination

showClaimStateComponent ::
    Monad m =>
    -- | component name
    String ->
    (SomeClaim -> OrPattern RewritingVariableName) ->
    Maybe ReplNode ->
    ReplM m ()
showClaimStateComponent name transformer maybeNode = do
    maybeClaimState <- getClaimStateAt maybeNode
    case maybeClaimState of
        Nothing -> putStrLn' "Invalid node!"
        Just (ReplNode node, config) -> do
            omit <- Lens.use (field @"omit")
            putStrLn' $ name <> " at node " <> show node <> " is:"
            prettyClaimStateComponent
                transformer
                omit
                config
                & tell

{- | Shows current omit list if passed 'Nothing'. Adds/removes from the list
 depending on whether the string already exists in the list or not.
-}
omitCell ::
    forall m.
    Monad m =>
    -- | Nothing to show current list, @Just str@ to add/remove to list
    Maybe String ->
    ReplM m ()
omitCell =
    \case
        Nothing -> showCells
        Just str -> addOrRemove str
  where
    showCells :: ReplM m ()
    showCells = do
        omit <- Lens.use (field @"omit")
        if Set.null omit
            then putStrLn' "Omit list is currently empty."
            else traverse_ putStrLn' omit

    addOrRemove :: String -> ReplM m ()
    addOrRemove str = field @"omit" %= toggle str

    toggle :: String -> Set String -> Set String
    toggle x xs
        | x `Set.member` xs = x `Set.delete` xs
        | otherwise = x `Set.insert` xs

{- | Shows all leaf nodes identifiers which are either stuck or can be
 evaluated further.
-}
showLeafs :: forall m. Monad m => ReplM m ()
showLeafs = do
    leafsByType <- sortLeafsByType <$> getInnerGraph
    case Map.foldMapWithKey showPair leafsByType of
        "" -> putStrLn' "No leafs found, proof is complete."
        xs -> putStrLn' xs
  where
    showPair :: NodeState -> [Graph.Node] -> String
    showPair ns xs = show ns <> ": " <> show xs

proofStatus :: forall m. Monad m => ReplM m ()
proofStatus = do
    proofs <- allProofs
    putStrLn' . showProofStatus $ proofs

allProofs ::
    forall m.
    Monad m =>
    ReplM m (Map.Map ClaimIndex GraphProofStatus)
allProofs = do
    graphs <- Lens.use (field @"graphs")
    claims <- Lens.use (field @"claims")
    let cindexes = ClaimIndex <$> [0 .. length claims - 1]
    return $
        Map.union
            (fmap inProgressProofs graphs)
            (notStartedProofs graphs (Map.fromList $ zip cindexes claims))
  where
    inProgressProofs ::
        ExecutionGraph ->
        GraphProofStatus
    inProgressProofs =
        findProofStatus
            . sortLeafsByType
            . Strategy.graph

    notStartedProofs ::
        Map.Map ClaimIndex ExecutionGraph ->
        Map.Map ClaimIndex SomeClaim ->
        Map.Map ClaimIndex GraphProofStatus
    notStartedProofs gphs cls =
        notStartedOrTrusted <$> cls `Map.difference` gphs

    notStartedOrTrusted :: SomeClaim -> GraphProofStatus
    notStartedOrTrusted cl =
        if isTrusted cl
            then TrustedClaim
            else NotStarted

    findProofStatus :: Map.Map NodeState [Graph.Node] -> GraphProofStatus
    findProofStatus m =
        case Map.lookup StuckNode m of
            Nothing ->
                case Map.lookup UnevaluatedNode m of
                    Nothing -> Completed
                    Just ns -> InProgress ns
            Just ns -> StuckProof ns

showRule ::
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    Maybe ReplNode ->
    m ()
showRule configNode = do
    maybeRule <- getRuleFor configNode
    case maybeRule of
        Nothing -> putStrLn' "Invalid node!"
        Just rule -> do
            tell . showRewriteRule $ rule
            putStrLn' $ showRuleIdentifier rule

showRules ::
    Monad m =>
    (ReplNode, ReplNode) ->
    ReplM m ()
showRules (ReplNode node1, ReplNode node2) = do
    graph <- getInnerGraph
    let path =
            Graph.lesp node1 node2 graph
                & Graph.unLPath
    case path of
        [] -> putStrLn' noPath
        [singleNode] ->
            getRuleFor (singleNode & fst & ReplNode & Just)
                >>= putStrLn' . maybe "Invalid node!" showRuleIdentifier
        (_ : labeledNodes) -> do
            let mapPath = Map.fromList labeledNodes
            putStrLn' $ Map.foldrWithKey acc "Rules applied:" mapPath
  where
    noPath =
        "There is no path between "
            <> show node1
            <> " and "
            <> show node2
            <> "."
    acc node rules result =
        result
            <> "\n  to reach node "
            <> show node
            <> " the following rules were applied:"
            <> case toList rules of
                [] -> " Implication checking."
                rules' -> foldr oneStepRuleIndexes "" rules'
    oneStepRuleIndexes rule result =
        result <> " " <> showRuleIdentifier rule

showRuleIdentifier ::
    From rule AttrLabel.Label =>
    From rule RuleIndex =>
    rule ->
    String
showRuleIdentifier rule =
    fromMaybe
        (showAxiomOrClaim ruleIndex)
        (showAxiomOrClaimName ruleIndex (getNameText rule))
  where
    ruleIndex = getInternalIdentifier rule

-- | Shows the previous branching point.
showPrecBranch ::
    Monad m =>
    -- | 'Nothing' for current node, or @Just n@ for a specific node identifier
    Maybe ReplNode ->
    ReplM m ()
showPrecBranch maybeNode = do
    graph <- getInnerGraph
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> putStrLn' "Invalid node!"
        Just node -> putStrLn' . show $ loop (loopCond graph) (unReplNode node)
  where
    -- "Left n" means continue looping with value being n
    -- "Right n" means "stop and return n"
    loopCond gph n
        | isNotBranch gph n && isNotRoot gph n = Left $ head (Graph.pre gph n)
        | otherwise = Right n

    isNotBranch gph n = Graph.outdeg gph n <= 1
    isNotRoot gph n = not . null . Graph.pre gph $ n

-- | Shows the next node(s) for the selected node.
showChildren ::
    Monad m =>
    -- | 'Nothing' for current node, or @Just n@ for a specific node identifier
    Maybe ReplNode ->
    ReplM m ()
showChildren maybeNode = do
    graph <- getInnerGraph
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> putStrLn' "Invalid node!"
        Just node -> putStrLn' . show . Graph.suc graph $ unReplNode node

-- | Shows existing labels or go to an existing label.
label ::
    forall m.
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    -- | 'Nothing' for show labels, @Just str@ for jumping to the string label.
    Maybe String ->
    m ()
label =
    \case
        Nothing -> showLabels
        Just lbl -> gotoLabel lbl
  where
    showLabels :: m ()
    showLabels = do
        lbls <- getLabels
        putStrLn' $ Map.foldrWithKey acc "Labels: " lbls

    gotoLabel :: String -> m ()
    gotoLabel l = do
        lbls <- getLabels
        selectNode $ fromMaybe (ReplNode $ -1) (Map.lookup l lbls)

    acc :: String -> ReplNode -> String -> String
    acc key node res =
        res <> "\n  " <> key <> ": " <> show (unReplNode node)

-- | Adds label for selected node.
labelAdd ::
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    -- | label
    String ->
    -- | 'Nothing' for current node, or @Just n@ for a specific node identifier
    Maybe ReplNode ->
    m ()
labelAdd lbl maybeNode = do
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> putStrLn' "Target node is not in the graph."
        Just node -> do
            labels <- getLabels
            if lbl `Map.notMember` labels
                then do
                    setLabels $ Map.insert lbl node labels
                    putStrLn' "Label added."
                else putStrLn' "Label already exists."

-- | Removes a label.
labelDel ::
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    -- | label
    String ->
    m ()
labelDel lbl = do
    labels <- getLabels
    if lbl `Map.member` labels
        then do
            setLabels $ Map.delete lbl labels
            putStrLn' "Removed label."
        else putStrLn' "Label doesn't exist."

-- | Redirect command to specified file.
redirect ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    -- | command to redirect
    ReplCommand ->
    -- | file path
    FilePath ->
    ReplM m ()
redirect cmd file = do
    liftIO $ withExistingDirectory file (`writeFile` "")
    appendCommand cmd file

runInterpreterWithOutput ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    PrintAuxOutput ->
    PrintKoreOutput ->
    ReplCommand ->
    Config m ->
    ReplM m ()
runInterpreterWithOutput printAux printKore cmd config =
    get
        >>= ( \st ->
                lift $
                    execStateReader config st $
                        replInterpreter0 printAux printKore cmd
            )
        >>= put

data AlsoApplyRule = Never | IfPossible

{- | Attempt to use a specific axiom or claim to see if it unifies with the
 current node.
-}
tryAxiomClaim ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    -- | tagged index in the axioms or claims list
    RuleReference ->
    ReplM m ()
tryAxiomClaim = tryAxiomClaimWorker Never

-- | Attempt to use a specific axiom or claim to progress the current proof.
tryFAxiomClaim ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    -- | tagged index in the axioms or claims list
    RuleReference ->
    ReplM m ()
tryFAxiomClaim = tryAxiomClaimWorker IfPossible

tryAxiomClaimWorker ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    AlsoApplyRule ->
    -- | tagged index in the axioms or claims list
    RuleReference ->
    ReplM m ()
tryAxiomClaimWorker mode ref = do
    maybeAxiomOrClaim <-
        ruleReference
            getAxiomOrClaimByIndex
            getAxiomOrClaimByName
            ref
    case maybeAxiomOrClaim of
        Nothing ->
            putStrLn' "Could not find axiom or claim."
        Just axiomOrClaim -> do
            claim <- Lens.use (field @"claim")
            if isSomeClaim claim && notEqualClaimTypes axiomOrClaim claim
                then
                    putStrLn'
                        "Only claims of the same type as the current\
                        \ claim can be applied as rewrite rules."
                else do
                    node <- Lens.use (field @"node")
                    case mode of
                        Never ->
                            showUnificationFailure axiomOrClaim node
                        IfPossible ->
                            tryForceAxiomOrClaim axiomOrClaim node
  where
    notEqualClaimTypes :: Either Axiom SomeClaim -> SomeClaim -> Bool
    notEqualClaimTypes axiomOrClaim' claim' =
        not (either (const True) (equalClaimTypes claim') axiomOrClaim')

    equalClaimTypes :: SomeClaim -> SomeClaim -> Bool
    equalClaimTypes =
        isSameType `on` castToReachability

    castToReachability :: SomeClaim -> Maybe SomeClaim
    castToReachability = Typeable.cast

    isSomeClaim :: SomeClaim -> Bool
    isSomeClaim = isJust . castToReachability

    isSameType ::
        Maybe SomeClaim ->
        Maybe SomeClaim ->
        Bool
    isSameType (Just (OnePath _)) (Just (OnePath _)) = True
    isSameType (Just (AllPath _)) (Just (AllPath _)) = True
    isSameType _ _ = False

    showUnificationFailure ::
        Either Axiom SomeClaim ->
        ReplNode ->
        ReplM m ()
    showUnificationFailure axiomOrClaim' node = do
        let first = extractLeftPattern axiomOrClaim'
        maybeSecond <- getClaimStateAt (Just node)
        case maybeSecond of
            Nothing -> putStrLn' "Unexpected error getting current config."
            Just (_, second) ->
                claimState
                    ClaimStateTransformer
                        { provenValue = putStrLn' "Cannot unify bottom"
                        , claimedTransformer = patternUnifier
                        , remainingTransformer = patternUnifier
                        , rewrittenTransformer = patternUnifier
                        , stuckTransformer = patternUnifier
                        }
                    (getConfiguration <$> second)
              where
                patternUnifier :: Pattern RewritingVariableName -> ReplM m ()
                patternUnifier
                    (Pattern.splitTerm -> (secondTerm, secondCondition)) =
                        runUnifier' sideCondition first secondTerm
                      where
                        sideCondition =
                            SideCondition.fromConditionWithReplacements
                                secondCondition

    tryForceAxiomOrClaim ::
        Either Axiom SomeClaim ->
        ReplNode ->
        ReplM m ()
    tryForceAxiomOrClaim axiomOrClaim node = do
        (graph, result) <-
            tryApplyAxiomOrClaim axiomOrClaim node
        case result of
            DoesNotApply ->
                showUnificationFailure axiomOrClaim node
            GetsProven -> do
                updateExecutionGraph graph
                putStrLn'
                    "The proof was proven without applying any rewrite rules."
            OneResult nextNode -> do
                updateExecutionGraph graph
                field @"node" .= nextNode
            MultipleResults ->
                updateExecutionGraph graph

    runUnifier' ::
        SideCondition RewritingVariableName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        ReplM m ()
    runUnifier' sideCondition first second =
        runUnifier sideCondition first' second
            >>= tell . formatUnificationMessage
      where
        first' = TermLike.refreshVariables (freeVariables second) first

    extractLeftPattern ::
        Either Axiom SomeClaim ->
        TermLike RewritingVariableName
    extractLeftPattern =
        either
            (RulePattern.left . coerce)
            (Pattern.toTermLike . getConfiguration)

-- | Removes specified node and all its child nodes.
clear ::
    forall m.
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    -- | 'Nothing' for current node, or @Just n@ for a specific node identifier
    Maybe ReplNode ->
    m ()
clear maybeNode = do
    graph <- getInnerGraph
    case maybeNode of
        Nothing -> Lens.use (field @"node") >>= clear . Just
        Just node
            | unReplNode node == 0 ->
                putStrLn' "Cannot clear initial node (0)."
            | isDirectDescendentOfBranching node graph ->
                putStrLn' "Cannot clear a direct descendant of a branching node."
            | otherwise -> clear0 node graph
  where
    clear0 :: ReplNode -> InnerGraph -> m ()
    clear0 rnode graph = do
        let node = unReplNode rnode
        let nodesToBeRemoved = collect (next graph) node
            graph' = Graph.delNodes nodesToBeRemoved graph
        updateInnerGraph graph'
        field @"node" .= ReplNode (prevNode graph' node)
        putStrLn' $ "Removed " <> show (length nodesToBeRemoved) <> " node(s)."

    next :: InnerGraph -> Graph.Node -> [Graph.Node]
    next gr n = fst <$> Graph.lsuc gr n

    collect :: (a -> [a]) -> a -> [a]
    collect f x = x : [z | y <- f x, z <- collect f y]

    prevNode :: InnerGraph -> Graph.Node -> Graph.Node
    prevNode graph = fromMaybe 0 . headMay . fmap fst . Graph.lpre graph

    isDirectDescendentOfBranching :: ReplNode -> InnerGraph -> Bool
    isDirectDescendentOfBranching (ReplNode node) graph =
        let childrenOfParent = (Graph.suc graph <=< Graph.pre graph) node
         in length childrenOfParent /= 1

-- | Save this sessions' commands to the specified file and tell "Done." after that.
saveSession ::
    forall m.
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    MonadIO m =>
    -- | path to file
    FilePath ->
    m ()
saveSession path = saveSessionWithMessage notifySuccess path
  where
    notifySuccess = putStrLn' "Done."

-- | Save this sessions' commands to the specified file and tell a message after that.
saveSessionWithMessage ::
    forall m.
    MonadState ReplState m =>
    MonadIO m =>
    -- | path to file
    m () ->
    FilePath ->
    m ()
saveSessionWithMessage notifySuccess path =
    withExistingDirectory path saveToFile
  where
    saveToFile :: FilePath -> m ()
    saveToFile file = do
        content <- seqUnlines <$> Lens.use (field @"commands")
        liftIO $ writeFile file content
        notifySuccess
    seqUnlines :: Seq String -> String
    seqUnlines = unlines . toList

savePartialProof ::
    forall m.
    MonadIO m =>
    Maybe Natural ->
    FilePath ->
    ReplM m ()
savePartialProof maybeNatural file = do
    currentIndex <- Lens.use (field @"claimIndex")
    claims <- Lens.use (field @"claims")
    Config{mainModuleName} <- ask
    maybeConfig <- getClaimStateAt maybeNode
    case (fmap . fmap) extractUnproven maybeConfig of
        Nothing -> putStrLn' "Invalid node!"
        Just (_, Nothing) -> putStrLn' "Goal is proven."
        Just (currentNode, Just currentGoal) -> do
            let newTrustedClaims =
                    makeTrusted
                        <$> removeIfRoot currentNode currentIndex claims
                newDefinition =
                    createNewDefinition
                        mainModuleName
                        (makeModuleName file)
                        $ currentGoal : newTrustedClaims
            saveUnparsedDefinitionToFile (unparse newDefinition)
            putStrLn' "Done."
  where
    saveUnparsedDefinitionToFile ::
        Pretty.Doc ann ->
        ReplM m ()
    saveUnparsedDefinitionToFile definition =
        liftIO $
            withFile
                (file <.> "kore")
                WriteMode
                (`Pretty.hPutDoc` definition)

    maybeNode :: Maybe ReplNode
    maybeNode =
        ReplNode . naturalToInt <$> maybeNatural

    removeIfRoot ::
        ReplNode ->
        ClaimIndex ->
        [SomeClaim] ->
        [SomeClaim]
    removeIfRoot (ReplNode node) (ClaimIndex index) claims
        | index >= 0 && index < length claims
          , node == 0 =
            take index claims
                <> drop (index + 1) claims
        | otherwise = claims

    makeModuleName :: FilePath -> String
    makeModuleName name = upper name <> "-SPEC"

{- | Pipe result of the command to the specified program.

This function will start one process for each KoreOut in the command's
output. AuxOut will not be piped, instead it will be sent directly to the repl's
output.
-}
pipe ::
    forall m.
    MonadIO m =>
    MonadSimplify m =>
    -- | command to pipe
    ReplCommand ->
    -- | path to the program that will receive the command's output
    String ->
    -- | additional arguments to be passed to the program
    [String] ->
    ReplM m ()
pipe cmd file args = do
    exists <- liftIO $ findExecutable file
    case exists of
        Nothing -> putStrLn' "Cannot find executable."
        Just exec -> do
            config <- ask
            pipeOutRef <- liftIO $ newIORef (mempty :: ReplOutput)
            runInterpreterWithOutput
                (PrintAuxOutput $ justPrint pipeOutRef)
                (PrintKoreOutput $ runExternalProcess pipeOutRef exec)
                cmd
                config
            pipeOut <- liftIO $ readIORef pipeOutRef
            tell pipeOut
  where
    createProcess' exec =
        liftIO $
            createProcess
                (proc exec args)
                    { std_in = CreatePipe
                    , std_out = CreatePipe
                    }
    runExternalProcess :: IORef ReplOutput -> String -> String -> IO ()
    runExternalProcess pipeOut exec str = do
        (maybeInput, maybeOutput, _, _) <- createProcess' exec
        let outputFunc = maybe putStrLn hPutStr maybeInput
        outputFunc str
        case maybeOutput of
            Nothing ->
                hPutStrLn stderr "Error: couldn't access output handle."
            Just handle -> do
                output <- liftIO $ hGetContents handle
                modifyIORef pipeOut (appReplOut . AuxOut $ output)
    justPrint :: IORef ReplOutput -> String -> IO ()
    justPrint outRef = modifyIORef outRef . appReplOut . AuxOut

-- | Appends output of a command to a file.
appendTo ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    -- | command
    ReplCommand ->
    -- | file to append to
    FilePath ->
    ReplM m ()
appendTo cmd file =
    withExistingDirectory file (appendCommand cmd)

appendCommand ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    ReplCommand ->
    FilePath ->
    ReplM m ()
appendCommand cmd file = do
    config <- ask
    runInterpreterWithOutput
        (PrintAuxOutput $ appendFile file)
        (PrintKoreOutput $ appendFile file)
        cmd
        config
    putStrLn' $ "Redirected output to \"" <> file <> "\"."

alias ::
    forall m.
    MonadState ReplState m =>
    MonadWriter ReplOutput m =>
    AliasDefinition ->
    m ()
alias a = do
    result <- runExceptT $ addOrUpdateAlias a
    case result of
        Left err -> putStrLn' $ showAliasError err
        Right _ -> pure ()

tryAlias ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    ReplAlias ->
    PrintAuxOutput ->
    PrintKoreOutput ->
    ReplM m ReplStatus
tryAlias replAlias@ReplAlias{name} printAux printKore = do
    res <- findAlias name
    case res of
        Nothing -> showUsage $> Continue
        Just aliasDef -> do
            let command = substituteAlias aliasDef replAlias
                parsedCommand =
                    fromMaybe
                        ShowUsage
                        $ parseMaybe commandParser (Text.pack command)
            config <- ask
            (cont, st') <- get >>= runInterpreter parsedCommand config
            put st'
            return cont
  where
    runInterpreter ::
        ReplCommand ->
        Config m ->
        ReplState ->
        ReplM m (ReplStatus, ReplState)
    runInterpreter cmd config st =
        lift $
            (`runStateT` st) $
                runReaderT
                    (replInterpreter0 printAux printKore cmd)
                    config

{- | Performs n proof steps, picking the next node unless branching occurs.
 Returns 'Left' while it has to continue looping, and 'Right' when done
 or when execution branches or proof finishes earlier than the counter.

 See 'loopM' for details.
-}
performStepNoBranching ::
    forall m.
    MonadSimplify m =>
    MonadIO m =>
    -- | (current step, last result)
    (Natural, StepResult) ->
    ReplM m (Either (Natural, StepResult) (Natural, StepResult))
performStepNoBranching =
    \case
        -- Termination branch
        (0, res) -> pure $ Right (0, res)
        -- Loop branch
        (n, SingleResult _) -> do
            res <- runStepper
            pure $ Left (n -1, res)
        -- Early exit when there is a branch or there is no next.
        (n, res) -> pure $ Right (n, res)

-- TODO(Vladimir): It would be ideal for this to be implemented in terms of
-- 'performStepNoBranching'.
recursiveForcedStep ::
    MonadSimplify m =>
    MonadIO m =>
    Natural ->
    ReplNode ->
    ReplM m ()
recursiveForcedStep n node
    | n == 0 = pure ()
    | otherwise = do
        ReplState{claims, axioms} <- get
        (graph, result) <- runStepper' claims axioms node
        updateExecutionGraph graph
        case result of
            NoResult -> pure ()
            SingleResult sr -> (recursiveForcedStep $ n -1) sr
            BranchResult xs -> traverse_ (recursiveForcedStep (n -1)) xs

-- | Display a rule as a String.
showRewriteRule ::
    Unparse rule =>
    From rule SourceLocation =>
    rule ->
    ReplOutput
showRewriteRule rule =
    makeKoreReplOutput (unparseToString rule)
        <> makeAuxReplOutput (show . Pretty.pretty . from @_ @SourceLocation $ rule)

-- | Pretty prints a strategy node, using an omit list to hide specified children.
prettyClaimStateComponent ::
    (SomeClaim -> OrPattern RewritingVariableName) ->
    -- | omit list
    Set String ->
    -- | pattern
    CommonClaimState ->
    ReplOutput
prettyClaimStateComponent transformation omitList =
    claimState
        ClaimStateTransformer
            { claimedTransformer =
                makeKoreReplOutput . prettyComponent
            , remainingTransformer =
                makeKoreReplOutput . prettyComponent
            , rewrittenTransformer =
                makeKoreReplOutput . prettyComponent
            , stuckTransformer = \goal ->
                makeAuxReplOutput "Stuck: \n"
                    <> makeKoreReplOutput (prettyComponent goal)
            , provenValue = makeAuxReplOutput "Proven."
            }
  where
    prettyComponent =
        unparseToString . OrPattern.toTermLike
            . MultiOr.map (fmap hide . getRewritingPattern)
            . transformation
    hide ::
        TermLike VariableName ->
        TermLike VariableName
    hide =
        Recursive.unfold $ \termLike ->
            case Recursive.project termLike of
                ann :< TermLike.ApplySymbolF app
                    | shouldBeExcluded (applicationSymbolOrAlias app) ->
                        -- Do not display children
                        ann :< TermLike.ApplySymbolF (withoutChildren app)
                projected -> projected

    withoutChildren app = app{applicationChildren = []}

    shouldBeExcluded =
        (`elem` omitList)
            . Text.unpack
            . Id.getId
            . TermLike.symbolConstructor

putStrLn' :: MonadWriter ReplOutput m => String -> m ()
putStrLn' = tell . makeAuxReplOutput

printIfNotEmpty :: String -> IO ()
printIfNotEmpty =
    \case
        "" -> pure ()
        xs -> putStr xs

printNotFound :: MonadWriter ReplOutput m => m ()
printNotFound = putStrLn' "Variable or index not found"

{- | Shows the 'dot' graph. This currently only works on Linux. The 'Int'
 parameter is needed in order to distinguish between axioms and claims and
 represents the number of available axioms.
-}
showDotGraph ::
    From axiom AttrLabel.Label =>
    From axiom RuleIndex =>
    Gr CommonClaimState (Maybe (Seq axiom)) ->
    IO ()
showDotGraph gr =
    flip Graph.runGraphvizCanvas' Graph.Xlib
        . Graph.graphToDot (graphParams gr)
        $ gr

saveDotGraph ::
    From axiom AttrLabel.Label =>
    From axiom RuleIndex =>
    Gr CommonClaimState (Maybe (Seq axiom)) ->
    Graph.GraphvizOutput ->
    FilePath ->
    IO ()
saveDotGraph gr format file =
    withExistingDirectory file saveGraphImg
  where
    saveGraphImg :: FilePath -> IO ()
    saveGraphImg path =
        void $
            Graph.addExtension
                ( Graph.runGraphviz
                    (Graph.graphToDot (graphParams gr) gr)
                )
                format
                path

graphParams ::
    From axiom AttrLabel.Label =>
    From axiom RuleIndex =>
    Gr CommonClaimState (Maybe (Seq axiom)) ->
    Graph.GraphvizParams
        Graph.Node
        CommonClaimState
        (Maybe (Seq axiom))
        ()
        CommonClaimState
graphParams gr =
    Graph.nonClusteredParams
        { Graph.fmtEdge = \(_, resN, l) ->
            [ Graph.textLabel (maybe "" (ruleIndex resN) l)
            , Graph.Attr.Style [dottedOrSolidEdge l]
            ]
        , Graph.fmtNode = \(_, ps) ->
            [ Graph.Attr.Color $
                case ps of
                    Proven -> toColorList green
                    Stuck _ -> toColorList red
                    _ -> []
            ]
        }
  where
    dottedOrSolidEdge lbl =
        maybe
            (Graph.Attr.SItem Graph.Attr.Dotted mempty)
            (const $ Graph.Attr.SItem Graph.Attr.Solid mempty)
            lbl
    ruleIndex resultNode lbl =
        let appliedRule = lbl & toList & headMay
            labelWithoutRule
                | isRemaining resultNode = "Remaining"
                | otherwise = "CheckImplication"
         in maybe
                labelWithoutRule
                (Text.Lazy.pack . showRuleIdentifier)
                appliedRule
    toColorList col = [Graph.Attr.WC col (Just 1.0)]
    green = Graph.Attr.RGB 0 200 0
    red = Graph.Attr.RGB 200 0 0
    isRemaining n =
        let (_, _, state, _) = Graph.context gr n
         in ClaimState.isRemaining state

showAliasError :: AliasError -> String
showAliasError =
    \case
        NameAlreadyDefined -> "Error: Alias name is already defined."
        UnknownCommand -> "Error: Command does not exist."

showAxiomOrClaim :: Attribute.RuleIndex -> String
showAxiomOrClaim (RuleIndex Nothing) =
    "Internal error: rule index was not initialized."
showAxiomOrClaim (RuleIndex (Just (Attribute.AxiomIndex ruleId))) =
    "Axiom " <> show ruleId
showAxiomOrClaim (RuleIndex (Just (Attribute.ClaimIndex ruleId))) =
    "Claim " <> show ruleId

showAxiomOrClaimName ::
    Attribute.RuleIndex ->
    AttrLabel.Label ->
    Maybe String
showAxiomOrClaimName _ (AttrLabel.Label Nothing) = Nothing
showAxiomOrClaimName (RuleIndex Nothing) _ = Nothing
showAxiomOrClaimName
    (RuleIndex (Just (Attribute.AxiomIndex _)))
    (AttrLabel.Label (Just ruleName)) =
        Just $ "Axiom " <> Text.unpack ruleName
showAxiomOrClaimName
    (RuleIndex (Just (Attribute.ClaimIndex _)))
    (AttrLabel.Label (Just ruleName)) =
        Just $ "Claim " <> Text.unpack ruleName

newtype ReplScriptParseError = ReplScriptParseError String
    deriving stock (Eq, Ord, Show)

instance ShowErrorComponent ReplScriptParseError where
    showErrorComponent (ReplScriptParseError err) = err

parseEvalScript ::
    forall t m.
    MonadSimplify m =>
    MonadIO m =>
    MonadState ReplState (t m) =>
    MonadReader (Config m) (t m) =>
    Monad.Trans.MonadTrans t =>
    FilePath ->
    ScriptModeOutput ->
    t m ()
parseEvalScript file scriptModeOutput = do
    exists <- lift . liftIO . doesFileExist $ file
    if exists
        then do
            contents <- lift . liftIO $ readFile file
            let result = runParser scriptParser file (Text.pack contents)
            either parseFailed executeScript result
        else lift . liftIO . hPutStrLn stderr $ "Cannot find " <> file
  where
    parseFailed err =
        lift . liftIO . hPutStrLn stderr $
            "\nCouldn't parse repl script file."
                <> "\nParser error at: "
                <> (err & toReplScriptParseErrors & errorBundlePretty)

    toReplScriptParseErrors errorBundle =
        errorBundle
            { bundleErrors =
                mapParseError (ReplScriptParseError . unReplParseError)
                    <$> bundleErrors errorBundle
            }

    executeScript ::
        [ReplCommand] ->
        t m ()
    executeScript cmds = do
        config <- ask
        get >>= executeCommands config >>= put
      where
        executeCommands config st =
            lift $
                execStateReader config st $
                    for_ cmds $
                        if scriptModeOutput == EnableOutput
                            then executeCommandWithOutput
                            else executeCommand

        executeCommand ::
            ReplCommand ->
            ReaderT (Config m) (StateT ReplState m) ReplStatus
        executeCommand command =
            replInterpreter0
                (PrintAuxOutput $ \_ -> return ())
                (PrintKoreOutput $ \_ -> return ())
                command

        executeCommandWithOutput ::
            ReplCommand ->
            ReaderT (Config m) (StateT ReplState m) ReplStatus
        executeCommandWithOutput command = do
            node <- Lens.use (field @"node")
            liftIO $ putStr $ "Kore (" <> show (unReplNode node) <> ")> "
            liftIO $ print command
            replInterpreter0
                (PrintAuxOutput printIfNotEmpty)
                (PrintKoreOutput printIfNotEmpty)
                command

formatUnificationMessage ::
    Maybe (NonEmpty (Condition RewritingVariableName)) ->
    ReplOutput
formatUnificationMessage docOrCondition =
    maybe mempty prettyUnifiers docOrCondition
  where
    prettyUnifiers =
        ReplOutput
            . (:) (AuxOut "Succeeded with unifiers:\n")
            . List.intersperse (AuxOut . show $ Pretty.indent 2 "and")
            . map (KoreOut . show . Pretty.indent 4 . unparseUnifier)
            . toList
    unparseUnifier c =
        unparse
            . Pattern.toTermLike
            $ TermLike.mkTop (TermLike.mkSortVariable "UNKNOWN") <$ c

showProofStatus :: Map.Map ClaimIndex GraphProofStatus -> String
showProofStatus m =
    Map.foldrWithKey acc "Current proof status: " m
  where
    acc :: ClaimIndex -> GraphProofStatus -> String -> String
    acc key elm res =
        res
            <> "\n  claim "
            <> (show . unClaimIndex) key
            <> ": "
            <> show elm

showCurrentClaimIndex :: ClaimIndex -> String
showCurrentClaimIndex ci =
    "You are currently proving claim "
        <> show (unClaimIndex ci)

execStateReader :: Monad m => env -> st -> ReaderT env (StateT st m) a -> m st
execStateReader config st = flip execStateT st . flip runReaderT config

doesParentDirectoryExist :: MonadIO m => FilePath -> m Bool
doesParentDirectoryExist =
    liftIO . doesDirectoryExist . fst . splitFileName

withExistingDirectory ::
    MonadIO m =>
    FilePath ->
    (FilePath -> m ()) ->
    m ()
withExistingDirectory path action =
    ifM
        (doesParentDirectoryExist path)
        (action path)
        $ liftIO . hPutStrLn stderr $ "Directory does not exist."
