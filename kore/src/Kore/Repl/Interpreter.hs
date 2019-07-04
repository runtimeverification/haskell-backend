{-|
Module      : Kore.Interpreter
Description : REPL interpreter
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl.Interpreter
    ( replInterpreter
    , showUsageMessage
    , showStepStoppedMessage
    , showProofStatus
    , showClaimSwitch
    , printIfNotEmpty
    , showRewriteRule
    , parseEvalScript
    , showAliasError
    , formatUnificationMessage
    , allProofs
    , ReplStatus(..)
    , showCurrentClaimIndex
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import           Control.Lens
                 ( (%=), (.=) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad
                 ( foldM, void )
import           Control.Monad.Extra
                 ( ifM, loop, loopM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.Reader
                 ( MonadReader, ReaderT (..) )
import qualified Control.Monad.Reader as Reader
                 ( ask )
import           Control.Monad.RWS.Strict
                 ( MonadWriter, RWST, ask, asks, lift, runRWST, tell )
import           Control.Monad.State.Class
                 ( get, put )
import           Control.Monad.State.Strict
                 ( MonadState, StateT (..), execStateT )
import qualified Control.Monad.Trans.Class as Monad.Trans
import           Control.Monad.Trans.Except
                 ( runExceptT )
import           Data.Coerce
                 ( Coercible, coerce )
import qualified Data.Foldable as Foldable
import           Data.Functor
                 ( ($>) )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.GraphViz as Graph
import           Data.IORef
                 ( IORef, modifyIORef, newIORef, readIORef )
import qualified Data.List as List
import           Data.List.NonEmpty
                 ( NonEmpty )
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( fromJust, listToMaybe )
import           Data.Sequence
                 ( Seq )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Exts
                 ( toList )
import           GHC.IO.Handle
                 ( hGetContents, hPutStr )
import           System.Exit

import           Kore.Attribute.Axiom
                 ( SourceLocation (..) )
import qualified Kore.Attribute.Axiom as Attribute
                 ( Axiom (..), RuleIndex (..), sourceLocation )
import qualified Kore.Attribute.Label as AttrLabel
import           Kore.Attribute.RuleIndex
import           Kore.Internal.Conditional
                 ( Conditional (..) )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.Predicate
                 ( Predicate )
import           Kore.Internal.TermLike
                 ( TermLike )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Logger as Logger
import           Kore.OnePath.StrategyPattern
                 ( CommonStrategyPattern,
                 StrategyPatternTransformer (StrategyPatternTransformer),
                 strategyPattern )
import qualified Kore.OnePath.StrategyPattern as StrategyPatternTransformer
                 ( StrategyPatternTransformer (..) )
import           Kore.OnePath.Verification
                 ( Axiom (..), Claim, isTrusted )
import           Kore.Repl.Data
import           Kore.Repl.Parser
import           Kore.Repl.Parser
                 ( commandParser )
import           Kore.Repl.State
import           Kore.Step.Rule
                 ( RewriteRule (..), RulePattern (..) )
import qualified Kore.Step.Rule as Rule
import qualified Kore.Step.Rule as Axiom
                 ( attributes )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Syntax.Application
import qualified Kore.Syntax.Id as Id
                 ( Id (..) )
import           Kore.Syntax.Variable
                 ( Variable )
import           Kore.Unparser
                 ( unparse, unparseToString )
import           Numeric.Natural
import           System.Directory
                 ( doesDirectoryExist, doesFileExist, findExecutable )
import           System.FilePath.Posix
                 ( splitFileName )
import           System.Process
                 ( StdStream (CreatePipe), createProcess, proc, std_in,
                 std_out )
import           Text.Megaparsec
                 ( ParseErrorBundle (..), errorBundlePretty, parseMaybe,
                 runParser )

-- | Warning: you should never use WriterT or RWST. It is used here with
-- _great care_ of evaluating the RWST to a StateT immediatly, and thus getting
-- rid of the WriterT part of the stack. This happens in the implementation of
-- 'replInterpreter'.
type ReplM claim m a = RWST (Config claim m) ReplOutput (ReplState claim) m a

data ReplStatus = Continue | SuccessStop | FailStop
    deriving (Eq, Show)

-- | Interprets a REPL command in a stateful Simplifier context.
replInterpreter
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => PrintAuxOutput
    -> PrintKoreOutput
    -> ReplCommand
    -> ReaderT (Config claim m) (StateT (ReplState claim) m) ReplStatus
replInterpreter printAux printKore replCmd = do
    let command = case replCmd of
                ShowUsage          -> showUsage          $> Continue
                Help               -> help               $> Continue
                ShowClaim mc       -> showClaim mc       $> Continue
                ShowAxiom ea       -> showAxiom ea       $> Continue
                Prove i            -> prove i            $> Continue
                ShowGraph mfile    -> showGraph mfile    $> Continue
                ProveSteps n       -> proveSteps n       $> Continue
                ProveStepsF n      -> proveStepsF n      $> Continue
                SelectNode i       -> selectNode i       $> Continue
                ShowConfig mc      -> showConfig mc      $> Continue
                OmitCell c         -> omitCell c         $> Continue
                ShowLeafs          -> showLeafs          $> Continue
                ShowRule   mc      -> showRule mc        $> Continue
                ShowPrecBranch mn  -> showPrecBranch mn  $> Continue
                ShowChildren mn    -> showChildren mn    $> Continue
                Label ms           -> label ms           $> Continue
                LabelAdd l mn      -> labelAdd l mn      $> Continue
                LabelDel l         -> labelDel l         $> Continue
                Redirect inn file  -> redirect inn file  $> Continue
                Try ref            -> tryAxiomClaim ref  $> Continue
                TryF ac            -> tryFAxiomClaim ac  $> Continue
                Clear n            -> clear n            $> Continue
                SaveSession file   -> saveSession file   $> Continue
                Pipe inn file args -> pipe inn file args $> Continue
                AppendTo inn file  -> appendTo inn file  $> Continue
                Alias a            -> alias a            $> Continue
                TryAlias name      -> tryAlias name printAux printKore
                LoadScript file    -> loadScript file    $> Continue
                ProofStatus        -> proofStatus        $> Continue
                Log s t            -> handleLog (s,t)    $> Continue
                Exit               -> exit
    (ReplOutput output, shouldContinue) <- evaluateCommand command
    liftIO $ Foldable.traverse_
            ( replOut
                (unPrintAuxOutput printAux)
                (unPrintKoreOutput printKore)
            )
            output
    case shouldContinue of
        Continue -> pure Continue
        SuccessStop -> liftIO exitSuccess
        FailStop -> liftIO . exitWith $ ExitFailure 2
  where
    -- Extracts the Writer out of the RWST monad using the current state
    -- and updates the state, returning the writer output along with the
    -- monadic result.
    evaluateCommand
        :: ReplM claim m ReplStatus
        -> ReaderT (Config claim m) (StateT (ReplState claim) m) (ReplOutput, ReplStatus)
    evaluateCommand c = do
        st <- get
        config <- Reader.ask
        (ext, st', w) <-
            Monad.Trans.lift
                $ Monad.Trans.lift
                $ runRWST c config st
        put st'
        pure (w, ext)

whichOutputFunc
    :: PrintAuxOutput
    -> PrintKoreOutput
    -> ReplOut
    -> IO ()
whichOutputFunc printAux printKore =
    \case
        AuxOut str  -> unPrintAuxOutput printAux $ str
        KoreOut str -> unPrintKoreOutput printKore $ str

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

exit
    :: Claim claim
    => MonadIO m
    => ReplM claim m ReplStatus
exit = do
    proofs <- allProofs
    ofile <- Lens.view lensOutputFile
    let fileName =
            maybe (error "Output file not specified") id (unOutputFile ofile)
    onePathClaims <- generateInProgressOPClaims
    sort <- currentClaimSort
    let conj = conjOfOnePathClaims onePathClaims sort
    liftIO $ writeFile
            fileName
            ( unparseToString
            . TermLike.externalizeFreshVariables
            $ conj
            )
    if isCompleted (Map.elems proofs)
       then return SuccessStop
       else return FailStop
  where
    isCompleted :: [GraphProofStatus] -> Bool
    isCompleted xs =
        foldr
            (&&)
            True
            (fmap (\x -> x == Completed || x == TrustedClaim) xs)

help :: MonadWriter ReplOutput m => m ()
help = putStrLn' helpText

-- | Prints a claim using an index in the claims list.
showClaim
    :: Claim claim
    => MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => Maybe (Either ClaimIndex RuleName)
    -> m ()
showClaim =
    \case
        Nothing -> do
            currentCindex <- Lens.use lensClaimIndex
            putStrLn' . showCurrentClaimIndex $ currentCindex
        Just indexOrName -> do
            claim <- either
                        (getClaimByIndex . unClaimIndex)
                        (getClaimByName . unRuleName)
                        indexOrName
            maybe printNotFound (tell . showRewriteRule) $ claim

-- | Prints an axiom using an index in the axioms list.
showAxiom
    :: MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => Either AxiomIndex RuleName
    -- ^ index in the axioms list
    -> m ()
showAxiom indexOrName = do
    axiom <- either
                (getAxiomByIndex . unAxiomIndex)
                (getAxiomByName . unRuleName)
                indexOrName
    maybe printNotFound (tell . showRewriteRule) $ axiom

-- | Changes the currently focused proof, using an index in the claims list.
prove
    :: forall claim m
    .  Claim claim
    => MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => Either ClaimIndex RuleName
    -- ^ index in the claims list
    -> m ()
prove indexOrName = do
    claim' <- either
                (getClaimByIndex . unClaimIndex)
                (getClaimByName . unRuleName)
                indexOrName
    maybe
        printNotFound
        startProving
        claim'
  where
    startProving
        :: claim
        -> m ()
    startProving claim = do
        if isTrusted claim
            then putStrLn'
                    $ "Cannot switch to proving claim "
                    <> showIndexOrName indexOrName
                    <> ". Claim is trusted."
            else do
                claimIndex <-
                    either
                        (return . return)
                        (getClaimIndexByName . unRuleName)
                        indexOrName
                switchToProof claim $ fromJust claimIndex
                putStrLn'
                    $ "Switched to proving claim "
                    <> showIndexOrName indexOrName

showClaimSwitch :: Either ClaimIndex RuleName -> String
showClaimSwitch indexOrName =
    "Switched to proving claim "
    <> showIndexOrName indexOrName

showIndexOrName
    :: Either ClaimIndex RuleName
    -> String
showIndexOrName =
        either (show . unClaimIndex) (show . unRuleName)

showGraph
    :: MonadIO m
    => MonadWriter ReplOutput m
    => Claim claim
    => Maybe FilePath
    -> MonadState (ReplState claim) m
    => m ()
showGraph mfile = do
    graph <- getInnerGraph
    axioms <- Lens.use lensAxioms
    installed <- liftIO Graph.isGraphvizInstalled
    if installed == True
       then liftIO $ maybe
                        (showDotGraph (length axioms) graph)
                        (saveDotGraph (length axioms) graph)
                        mfile
       else putStrLn' "Graphviz is not installed."

-- | Executes 'n' prove steps, or until branching occurs.
proveSteps
    :: Claim claim
    => MonadSimplify m
    => MonadIO m
    => Natural
    -- ^ maximum number of steps to perform
    -> ReplM claim m ()
proveSteps n = do
    let node = ReplNode . fromEnum $ n
    result <- loopM performStepNoBranching (n, SingleResult node)
    case result of
        (0, SingleResult _) -> pure ()
        (done, res) ->
            putStrLn' $ showStepStoppedMessage (n - done - 1) res

-- | Executes 'n' prove steps, distributing over branches. It will perform less
-- than 'n' steps if the proof is stuck or completed in less than 'n' steps.
proveStepsF
    :: Claim claim
    => Monad m
    => Natural
    -- ^ maximum number of steps to perform
    -> ReplM claim m ()
proveStepsF n = do
    graph  <- getExecutionGraph
    node   <- Lens.use lensNode
    graph' <- recursiveForcedStep n graph node
    updateExecutionGraph graph'

-- | Loads a script from a file.
loadScript
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => FilePath
    -- ^ path to file
    -> ReplM claim m ()
loadScript file = parseEvalScript file

handleLog
    :: MonadState (ReplState claim) m
    => (Logger.Severity, LogType)
    -> m ()
handleLog t = lensLogging .= t

-- | Focuses the node with id equals to 'n'.
selectNode
    :: MonadState (ReplState claim) m
    => Claim claim
    => MonadWriter ReplOutput m
    => ReplNode
    -- ^ node identifier
    -> m ()
selectNode rnode = do
    graph <- getInnerGraph
    let i = unReplNode rnode
    if i `elem` Graph.nodes graph
        then lensNode .= rnode
        else putStrLn' "Invalid node!"

-- | Shows configuration at node 'n', or current node if 'Nothing' is passed.
showConfig
    :: Claim claim
    => Monad m
    => Maybe ReplNode
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim m ()
showConfig configNode = do
    maybeConfig <- getConfigAt configNode
    case maybeConfig of
        Nothing -> putStrLn' "Invalid node!"
        Just (ReplNode node, config) -> do
            omit <- Lens.use lensOmit
            putStrLn' $ "Config at node " <> show node <> " is:"
            tell $ unparseStrategy omit config

-- | Shows current omit list if passed 'Nothing'. Adds/removes from the list
-- depending on whether the string already exists in the list or not.
omitCell
    :: forall claim m
    .  Monad m
    => Maybe String
    -- ^ Nothing to show current list, @Just str@ to add/remove to list
    -> ReplM claim m ()
omitCell =
    \case
        Nothing  -> showCells
        Just str -> addOrRemove str
  where
    showCells :: ReplM claim m ()
    showCells = do
        omit <- Lens.use lensOmit
        if Set.null omit
            then putStrLn' "Omit list is currently empty."
            else Foldable.traverse_ putStrLn' omit

    addOrRemove :: String -> ReplM claim m ()
    addOrRemove str = lensOmit %= toggle str

    toggle :: String -> Set String -> Set String
    toggle x xs
      | x `Set.member` xs = x `Set.delete` xs
      | otherwise         = x `Set.insert` xs

-- | Shows all leaf nodes identifiers which are either stuck or can be
-- evaluated further.
showLeafs
    :: forall claim m
    .  Claim claim
    => Monad m
    => ReplM claim m ()
showLeafs = do
    leafsByType <- sortLeafsByType <$> getInnerGraph
    case Map.foldMapWithKey showPair leafsByType of
        "" -> putStrLn' "No leafs found, proof is complete."
        xs -> putStrLn' xs
  where
    showPair :: NodeState -> [Graph.Node] -> String
    showPair ns xs = show ns <> ": " <> show xs

proofStatus
    :: forall claim m
    .  Claim claim
    => Monad m
    => ReplM claim m ()
proofStatus = do
    proofs <- allProofs
    putStrLn' . showProofStatus $ proofs

allProofs
    :: forall claim m
    .  Claim claim
    => Monad m
    => ReplM claim m (Map.Map ClaimIndex GraphProofStatus)
allProofs = do
    graphs <- Lens.use lensGraphs
    claims <- Lens.use lensClaims
    let cindexes = ClaimIndex <$> [0..length claims - 1]
    return
        $ Map.union
            (fmap inProgressProofs graphs)
            (notStartedProofs graphs (Map.fromList $ zip cindexes claims))
  where
    inProgressProofs
        :: ExecutionGraph
        -> GraphProofStatus
    inProgressProofs =
        findProofStatus
        . sortLeafsByType
        . Strategy.graph

    notStartedProofs
        :: Claim claim
        => Map.Map ClaimIndex ExecutionGraph
        -> Map.Map ClaimIndex claim
        -> Map.Map ClaimIndex GraphProofStatus
    notStartedProofs gphs cls =
        notStartedOrTrusted <$> cls `Map.difference` gphs

    notStartedOrTrusted :: claim -> GraphProofStatus
    notStartedOrTrusted cl =
        if isTrusted cl
           then TrustedClaim
           else NotStarted

    findProofStatus :: Map.Map NodeState [Graph.Node] -> GraphProofStatus
    findProofStatus m =
        case Map.lookup StuckNode m of
            Nothing -> case Map.lookup UnevaluatedNode m of
                           Nothing -> Completed
                           Just ns -> InProgress ns
            Just ns -> StuckProof ns

showRule
    :: MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => Claim claim
    => Maybe ReplNode
    -> m ()
showRule configNode = do
    maybeRule <- getRuleFor configNode
    case maybeRule of
        Nothing -> putStrLn' "Invalid node!"
        Just rule -> do
            axioms <- Lens.use lensAxioms
            tell . showRewriteRule $ rule
            let ruleIndex = getRuleIndex rule
            putStrLn' $ maybe
                "Error: identifier attribute wasn't initialized."
                id
                (showAxiomOrClaim (length axioms) ruleIndex)
  where
    getRuleIndex :: RewriteRule Variable -> Attribute.RuleIndex
    getRuleIndex = Attribute.identifier . Rule.attributes . Rule.getRewriteRule

-- | Shows the previous branching point.
showPrecBranch
    :: Claim claim
    => Monad m
    => Maybe ReplNode
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim m ()
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
showChildren
    :: Claim claim
    => Monad m
    => Maybe ReplNode
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim m ()
showChildren maybeNode = do
    graph <- getInnerGraph
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> putStrLn' "Invalid node!"
        Just node -> putStrLn' . show . Graph.suc graph $ unReplNode node

-- | Shows existing labels or go to an existing label.
label
    :: forall m claim
    .  MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => Claim claim
    => Maybe String
    -- ^ 'Nothing' for show labels, @Just str@ for jumping to the string label.
    -> m ()
label =
    \case
        Nothing  -> showLabels
        Just lbl -> gotoLabel lbl
  where
    showLabels :: m ()
    showLabels = do
        lbls <- getLabels
        putStrLn' $ Map.foldrWithKey acc "Labels: " lbls

    gotoLabel :: String -> m ()
    gotoLabel l = do
        lbls <- getLabels
        selectNode $ maybe (ReplNode $ -1) id (Map.lookup l lbls)

    acc :: String -> ReplNode -> String -> String
    acc key node res =
        res <> "\n  " <> key <> ": " <> show (unReplNode node)

-- | Adds label for selected node.
labelAdd
    :: MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => Claim claim
    => String
    -- ^ label
    -> Maybe ReplNode
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> m ()
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
                else
                    putStrLn' "Label already exists."

-- | Removes a label.
labelDel
    :: MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => String
    -- ^ label
    -> m ()
labelDel lbl = do
    labels <- getLabels
    if lbl `Map.member` labels
       then do
           setLabels $ Map.delete lbl labels
           putStrLn' "Removed label."
       else
           putStrLn' "Label doesn't exist."

outputsKore :: ReplCommand -> Bool
outputsKore =
    \case
        ShowClaim _  -> True
        ShowAxiom _  -> True
        ShowConfig _ -> True
        ShowRule _   -> True
        Try _        -> True
        TryF _       -> True
        _            -> False

-- | Redirect command to specified file.
redirect
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => ReplCommand
    -- ^ command to redirect
    -> FilePath
    -- ^ file path
    -> ReplM claim m ()
redirect cmd file = do
    liftIO $ whenPathIsReachable file (flip writeFile $ "")
    appendCommand cmd file

runInterpreterWithOutput
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => PrintAuxOutput
    -> PrintKoreOutput
    -> ReplCommand
    -> Config claim m
    -> ReplM claim m ()
runInterpreterWithOutput printAux printKore cmd config =
    get >>= (\st -> lift
            $ execStateReader config st
            $ replInterpreter printAux printKore cmd
            )
        >>= put

data AlsoApplyRule = Never | IfPossible

-- | Attempt to use a specific axiom or claim to see if it unifies with the
-- current node.
tryAxiomClaim
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => RuleReference
    -- ^ tagged index in the axioms or claims list
    -> ReplM claim m ()
tryAxiomClaim = tryAxiomClaimWorker Never

-- | Attempt to use a specific axiom or claim to progress the current proof.
tryFAxiomClaim
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => RuleReference
    -- ^ tagged index in the axioms or claims list
    -> ReplM claim m ()
tryFAxiomClaim = tryAxiomClaimWorker IfPossible

tryAxiomClaimWorker
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => AlsoApplyRule
    -> RuleReference
    -- ^ tagged index in the axioms or claims list
    -> ReplM claim m ()
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
           node <- Lens.use lensNode
           case mode of
               Never ->
                   showUnificationFailure axiomOrClaim node
               IfPossible ->
                   tryForceAxiomOrClaim axiomOrClaim node
  where
    showUnificationFailure
        :: Either Axiom claim
        -> ReplNode
        -> ReplM claim m ()
    showUnificationFailure axiomOrClaim' node = do
        let first = extractLeftPattern axiomOrClaim'
        maybeSecond <- getConfigAt (Just node)
        case maybeSecond of
            Nothing -> putStrLn' "Unexpected error getting current config."
            Just (_, second) ->
                strategyPattern
                    StrategyPatternTransformer
                        { bottomValue        = putStrLn' "Cannot unify bottom"
                        , rewriteTransformer = runUnifier' first . term
                        , stuckTransformer   = runUnifier' first . term
                        }
                    second

    tryForceAxiomOrClaim
        :: Either Axiom claim
        -> ReplNode
        -> ReplM claim m ()
    tryForceAxiomOrClaim axiomOrClaim node = do
        (graph, result) <-
            runStepper'
                (either mempty pure   axiomOrClaim)
                (either pure   mempty axiomOrClaim)
                node
        case result of
            NoResult ->
                showUnificationFailure axiomOrClaim node
            SingleResult nextNode -> do
                updateExecutionGraph graph
                lensNode .= nextNode
            BranchResult _ ->
                updateExecutionGraph graph

    runUnifier'
        :: TermLike Variable
        -> TermLike Variable
        -> ReplM claim m ()
    runUnifier' first second =
        runUnifier first second
        >>= tell . formatUnificationMessage

    extractLeftPattern
        :: Either (Axiom) claim
        -> TermLike Variable
    extractLeftPattern =
            left . getRewriteRule . either unAxiom coerce

-- | Removes specified node and all its child nodes.
clear
    :: forall m claim
    .  MonadState (ReplState claim) m
    => Claim claim
    => MonadWriter ReplOutput m
    => Maybe ReplNode
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> m ()
clear =
    \case
        Nothing -> Just <$> Lens.use lensNode >>= clear
        Just node
          | unReplNode node == 0 -> putStrLn' "Cannot clear initial node (0)."
          | otherwise -> clear0 node
  where
    clear0 :: ReplNode -> m ()
    clear0 rnode = do
        graph <- getInnerGraph
        let node = unReplNode rnode
        let
            nodesToBeRemoved = collect (next graph) node
            graph' = Graph.delNodes nodesToBeRemoved graph
        updateInnerGraph graph'
        lensNode .= ReplNode (prevNode graph' node)
        putStrLn' $ "Removed " <> show (length nodesToBeRemoved) <> " node(s)."

    next :: InnerGraph -> Graph.Node -> [Graph.Node]
    next gr n = fst <$> Graph.lsuc gr n

    collect :: (a -> [a]) -> a -> [a]
    collect f x = x : [ z | y <- f x, z <- collect f y]

    prevNode :: InnerGraph -> Graph.Node -> Graph.Node
    prevNode graph = maybe 0 id . listToMaybe . fmap fst . Graph.lpre graph

-- | Save this sessions' commands to the specified file.
saveSession
    :: forall m
    .  forall claim
    .  MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => MonadIO m
    => FilePath
    -- ^ path to file
    -> m ()
saveSession path =
    whenPathIsReachable path saveToFile
  where
    saveToFile :: FilePath -> m ()
    saveToFile file = do
        content <- seqUnlines <$> Lens.use lensCommands
        liftIO $ writeFile file content
        putStrLn' "Done."
    seqUnlines :: Seq String -> String
    seqUnlines = unlines . toList

-- | Pipe result of command to specified program.
pipe
    :: forall claim m
    .  Claim claim
    => MonadIO m
    => MonadSimplify m
    => ReplCommand
    -- ^ command to pipe
    -> String
    -- ^ path to the program that will receive the command's output
    -> [String]
    -- ^ additional arguments to be passed to the program
    -> ReplM claim m ()
pipe cmd file args = do
    exists <- liftIO $ findExecutable file
    case exists of
        Nothing -> putStrLn' "Cannot find executable."
        Just exec -> do
            config <- ask
            pipeOutRef <- liftIO $ newIORef (mempty :: ReplOutput)
            if outputsKore cmd
                then
                    runInterpreterWithOutput
                        (PrintAuxOutput $ justPrint pipeOutRef)
                        (PrintKoreOutput $ runExternalProcess pipeOutRef exec)
                        cmd
                        config
                else
                    runInterpreterWithOutput
                        (PrintAuxOutput $ runExternalProcess pipeOutRef exec)
                        (PrintKoreOutput $ justPrint pipeOutRef)
                        cmd
                        config
            pipeOut <- liftIO $ readIORef pipeOutRef
            tell pipeOut
  where
    createProcess' exec =
        liftIO $ createProcess (proc exec args)
            { std_in = CreatePipe, std_out = CreatePipe }
    runExternalProcess :: IORef ReplOutput -> String -> String -> IO ()
    runExternalProcess pipeOut exec str = do
        (maybeInput, maybeOutput, _, _) <- createProcess' exec
        let outputFunc = maybe putStrLn hPutStr maybeInput
        outputFunc str
        case maybeOutput of
            Nothing ->
                putStrLn "Error: couldn't access output handle."
            Just handle -> do
                output <- liftIO $ hGetContents handle
                modifyIORef pipeOut (appReplOut . AuxOut $ output)
    justPrint :: IORef ReplOutput -> String -> IO ()
    justPrint outRef str = do
        modifyIORef outRef (appReplOut . AuxOut $ str)

-- | Appends output of a command to a file.
appendTo
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => ReplCommand
    -- ^ command
    -> FilePath
    -- ^ file to append to
    -> ReplM claim m ()
appendTo cmd file =
    whenPathIsReachable file (appendCommand cmd)

appendCommand
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => ReplCommand
    -> FilePath
    -> ReplM claim m ()
appendCommand cmd file = do
    config <- ask
    if outputsKore cmd
        then
            runInterpreterWithOutput
                (PrintAuxOutput $ \_ -> return () )
                (PrintKoreOutput $ appendFile file)
                cmd
                config
        else
            runInterpreterWithOutput
                (PrintAuxOutput $ appendFile file)
                (PrintKoreOutput $ \_ -> return () )
                cmd
                config
    putStrLn' $ "Redirected output to \"" <> file <> "\"."

alias
    :: forall m claim
    .  MonadState (ReplState claim) m
    => MonadWriter ReplOutput m
    => AliasDefinition
    -> m ()
alias a = do
    result <- runExceptT $ addOrUpdateAlias a
    case result of
        Left err -> putStrLn' $ showAliasError err
        Right _  -> pure ()

tryAlias
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => ReplAlias
    -> PrintAuxOutput
    -> PrintKoreOutput
    -> ReplM claim m ReplStatus
tryAlias replAlias@ReplAlias { name } printAux printKore = do
    res <- findAlias name
    case res of
        Nothing  -> showUsage $> Continue
        Just aliasDef -> do
            let
                command = substituteAlias aliasDef replAlias
                parsedCommand =
                    maybe ShowUsage id $ parseMaybe commandParser command
            config <- ask
            (cont, st') <- get >>= runInterpreter parsedCommand config
            put st'
            return cont
  where
    runInterpreter
        :: ReplCommand
        -> Config claim m
        -> ReplState claim
        -> ReplM claim m (ReplStatus, ReplState claim)
    runInterpreter cmd config st =
        lift
            $ (`runStateT` st)
            $ runReaderT (replInterpreter printAux printKore cmd) config

-- | Performs n proof steps, picking the next node unless branching occurs.
-- Returns 'Left' while it has to continue looping, and 'Right' when done
-- or when execution branches or proof finishes earlier than the counter.
--
-- See 'loopM' for details.
performStepNoBranching
    :: forall claim m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => (Natural, StepResult)
    -- ^ (current step, last result)
    -> ReplM claim m (Either (Natural, StepResult) (Natural, StepResult))
performStepNoBranching =
    \case
        -- Termination branch
        (0, res) -> pure $ Right (0, res)
        -- Loop branch
        (n, SingleResult _) -> do
            res <- runStepper
            pure $ Left (n-1, res)
        -- Early exit when there is a branch or there is no next.
        (n, res) -> pure $ Right (n, res)

-- TODO(Vladimir): It would be ideal for this to be implemented in terms of
-- 'performStepNoBranching'.
recursiveForcedStep
    :: Claim claim
    => Monad m
    => Natural
    -> ExecutionGraph
    -> ReplNode
    -> ReplM claim m ExecutionGraph
recursiveForcedStep n graph node
  | n == 0    = return graph
  | otherwise = do
      ReplState { claims , axioms , claim } <- get
      stepper <- asks stepper
      graph'@Strategy.ExecutionGraph { graph = gr } <-
          lift $ stepper claim claims axioms graph node
      case Graph.suc gr (unReplNode node) of
          [] -> return graph'
          xs -> foldM (recursiveForcedStep $ n-1) graph' (fmap ReplNode xs)

-- | Display a rule as a String.
showRewriteRule
    :: Coercible (RewriteRule Variable) rule
    => rule
    -> ReplOutput
showRewriteRule rule =
    makeKoreReplOutput (unparseToString rule')
    <> makeAuxReplOutput
        (show . Pretty.pretty . extractSourceAndLocation $ rule')
  where
    rule' = coerce rule

    extractSourceAndLocation
        :: RewriteRule Variable
        -> SourceLocation
    extractSourceAndLocation
        (RewriteRule (RulePattern{ Axiom.attributes })) =
            Attribute.sourceLocation attributes

-- | Unparses a strategy node, using an omit list to hide specified children.
unparseStrategy
    :: Set String
    -- ^ omit list
    -> CommonStrategyPattern
    -- ^ pattern
    -> ReplOutput
unparseStrategy omitList =
    strategyPattern StrategyPatternTransformer
        { rewriteTransformer = \pat ->
            makeKoreReplOutput
            . unparseToString
            . TermLike.externalizeFreshVariables
            . Pattern.toTermLike
            $ fmap hide pat
        , stuckTransformer =
            \pat -> makeAuxReplOutput "Stuck: \n"
                    <> makeKoreReplOutput
                    ( unparseToString
                     . TermLike.externalizeFreshVariables
                     . Pattern.toTermLike
                     $ fmap hide pat
                    )
        , bottomValue = makeAuxReplOutput "Reached bottom"
        }
  where
    hide :: TermLike Variable -> TermLike Variable
    hide =
        Recursive.unfold $ \termLike ->
            case Recursive.project termLike of
                ann :< TermLike.ApplySymbolF app
                  | shouldBeExcluded (applicationSymbolOrAlias app) ->
                    -- Do not display children
                    ann :< TermLike.ApplySymbolF (withoutChildren app)
                projected -> projected

    withoutChildren app = app { applicationChildren = [] }

    shouldBeExcluded =
       (`elem` omitList)
           . Text.unpack
           . Id.getId
           . TermLike.symbolConstructor

putStrLn' :: MonadWriter ReplOutput m => String -> m ()
putStrLn' str =
    tell . makeAuxReplOutput $ str

printIfNotEmpty :: String -> IO ()
printIfNotEmpty =
    \case
        "" -> pure ()
        xs -> putStrLn xs

printNotFound :: MonadWriter ReplOutput m => m ()
printNotFound = putStrLn' "Variable or index not found"

-- | Shows the 'dot' graph. This currently only works on Linux. The 'Int'
-- parameter is needed in order to distinguish between axioms and claims and
-- represents the number of available axioms.
showDotGraph :: Int -> InnerGraph -> IO ()
showDotGraph len =
    (flip Graph.runGraphvizCanvas') Graph.Xlib
        . Graph.graphToDot (graphParams len)

saveDotGraph :: Int -> InnerGraph -> FilePath -> IO ()
saveDotGraph len gr file =
    whenPathIsReachable file saveGraphImg
  where
    saveGraphImg :: FilePath -> IO ()
    saveGraphImg path =
        void
        . Graph.runGraphviz
            (Graph.graphToDot (graphParams len) gr) Graph.Jpeg
        $ path <> ".jpeg"

graphParams
    :: Int
    -> Graph.GraphvizParams
         Graph.Node
         CommonStrategyPattern
         (Seq (RewriteRule Variable))
         ()
         CommonStrategyPattern
graphParams len = Graph.nonClusteredParams
    { Graph.fmtEdge = \(_, _, l) ->
        [Graph.textLabel (ruleIndex l len)]
    }
  where
    ruleIndex lbl ln =
        case listToMaybe . toList $ lbl of
            Nothing -> "Simpl/RD"
            Just rule ->
                maybe
                    ( maybe "Unknown"
                        Text.Lazy.pack
                        ( showAxiomOrClaim ln
                        . getInternalIdentifier
                        $ rule
                        )
                    )
                    Text.Lazy.fromStrict
                    ( showAxiomOrClaimName ln (getInternalIdentifier rule)
                    . getNameText
                    $ rule
                    )

showAliasError :: AliasError -> String
showAliasError =
    \case
        NameAlreadyDefined -> "Error: Alias name is already defined."
        UnknownCommand     -> "Error: Command does not exist."

showAxiomOrClaim :: Int -> Attribute.RuleIndex -> Maybe String
showAxiomOrClaim _   (RuleIndex Nothing) = Nothing
showAxiomOrClaim len (RuleIndex (Just rid))
  | rid < len = Just $ "Axiom " <> show rid
  | otherwise = Just $ "Claim " <> show (rid - len)

showAxiomOrClaimName
    :: Int
    -> Attribute.RuleIndex
    -> AttrLabel.Label
    -> Maybe Text.Text
showAxiomOrClaimName _ _ (AttrLabel.Label Nothing) = Nothing
showAxiomOrClaimName _ (RuleIndex Nothing) _ = Nothing
showAxiomOrClaimName
    len
    (RuleIndex (Just rid))
    (AttrLabel.Label (Just ruleName))
  | rid < len = Just $ "Axiom " <> ruleName
  | otherwise = Just $ "Claim " <> ruleName

parseEvalScript
    :: forall claim t m
    .  Claim claim
    => MonadSimplify m
    => MonadIO m
    => MonadState (ReplState claim) (t m)
    => MonadReader (Config claim m) (t m)
    => Monad.Trans.MonadTrans t
    => FilePath
    -> t m ()
parseEvalScript file = do
    exists <- lift . liftIO . doesFileExist $ file
    if exists == True
        then do
            contents <- lift . liftIO $ readFile file
            let result = runParser scriptParser file contents
            either parseFailed executeScript result
        else do
            lift . liftIO . putStrLn
                $ "Cannot find " <> file

  where
    parseFailed
        :: ParseErrorBundle String String
        -> t m ()
    parseFailed err =
        lift . liftIO . putStrLn
            $ "\nCouldn't parse initial script file."
            <> "\nParser error at: "
            <> errorBundlePretty err

    executeScript
        :: [ReplCommand]
        -> t m ()
    executeScript cmds = do
        config <- ask
        get >>= executeCommands config >>= put
      where
        executeCommands config st =
           lift
               $ execStateReader config st
               $ Foldable.for_ cmds
               $ replInterpreter
                    (PrintAuxOutput $ \_ -> return ())
                    (PrintKoreOutput $ \_ -> return ())

formatUnificationMessage
    :: Either ReplOutput (NonEmpty (Predicate Variable))
    -> ReplOutput
formatUnificationMessage docOrPredicate =
    either id prettyUnifiers docOrPredicate
  where
    prettyUnifiers =
        ReplOutput
        . (:) (AuxOut "Succeeded with unifiers:")
        . List.intersperse (AuxOut . show $ Pretty.indent 2 "and")
        . map (KoreOut . show . Pretty.indent 4 . unparseUnifier)
        . Foldable.toList
    unparseUnifier c =
        unparse
        . TermLike.externalizeFreshVariables
        . Pattern.toTermLike
        $ (TermLike.mkTop $ TermLike.mkSortVariable "UNKNOWN")
        <$ c

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
execStateReader config st action =
    flip execStateT st
        $ flip runReaderT config
        $ action

checkIfCorrectFilePath :: MonadIO m => FilePath -> m Bool
checkIfCorrectFilePath =
    liftIO . doesDirectoryExist . fst . splitFileName

whenPathIsReachable
    :: MonadIO m
    => FilePath
    -> (FilePath -> m ())
    -> m ()
whenPathIsReachable path action =
    ifM
        (checkIfCorrectFilePath path)
        (action path)
        $ liftIO . putStrLn $ "Directory does not exist."
