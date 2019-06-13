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
                 ( foldM, join, void )
import           Control.Monad.Extra
                 ( loop, loopM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.RWS.Strict
                 ( MonadWriter, RWST, lift, runRWST, tell )
import           Control.Monad.State.Class
                 ( get, put )
import           Control.Monad.State.Strict
                 ( MonadState, StateT (..), execStateT )
import qualified Control.Monad.Trans.Class as Monad.Trans
import           Control.Monad.Trans.Except
                 ( runExceptT )
import           Data.Coerce
                 ( Coercible, coerce )
import qualified Data.Default as Default
import           Data.Foldable
                 ( traverse_ )
import           Data.Functor
                 ( ($>) )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.GraphViz as Graph
import           Data.List.Extra
                 ( groupSort )
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( fromJust )
import           Data.Maybe
                 ( catMaybes, listToMaybe )
import           Data.Sequence
                 ( Seq )
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
import           Kore.Attribute.RuleIndex
import           Kore.Internal.Pattern
                 ( Conditional (..), toTermLike )
import           Kore.Internal.TermLike
                 ( TermLike, termLikeSort )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Logger as Logger
import           Kore.OnePath.StrategyPattern
                 ( CommonStrategyPattern, StrategyPattern (..),
                 StrategyPatternTransformer (StrategyPatternTransformer),
                 extractUnproven, strategyPattern )
import qualified Kore.OnePath.StrategyPattern as StrategyPatternTransformer
                 ( StrategyPatternTransformer (..) )
import           Kore.OnePath.Verification
                 ( Axiom (..), Claim, isTrusted )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Repl.Data
import           Kore.Repl.Parser
import           Kore.Repl.Parser
                 ( commandParser )
import           Kore.Step.Rule
                 ( RewriteRule (..), RulePattern (..) )
import qualified Kore.Step.Rule as Rule
import qualified Kore.Step.Rule as Axiom
                 ( attributes )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Syntax.Application
import qualified Kore.Syntax.Id as Id
                 ( Id (..) )
import           Kore.Syntax.Variable
                 ( Variable )
import           Kore.Unparser
                 ( unparseToString )
import           Numeric.Natural
import           System.Directory
                 ( doesFileExist, findExecutable )
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
type ReplM claim a = RWST () String (ReplState claim) Simplifier a

data ReplStatus = Continue | SuccessStop | FailStop
    deriving (Eq, Show)

-- | Interprets a REPL command in a stateful Simplifier context.
replInterpreter
    :: forall claim
    .  Claim claim
    => (String -> IO ())
    -> ReplCommand
    -> StateT (ReplState claim) Simplifier ReplStatus
replInterpreter printFn replCmd = do
    let command = case replCmd of
                ShowUsage          -> showUsage          $> Continue
                Help               -> help               $> Continue
                ShowClaim mc       -> showClaim mc       $> Continue
                ShowAxiom a        -> showAxiom a        $> Continue
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
                Try ac             -> tryAxiomClaim ac   $> Continue
                Clear n            -> clear n            $> Continue
                SaveSession file   -> saveSession file   $> Continue
                Pipe inn file args -> pipe inn file args $> Continue
                AppendTo inn file  -> appendTo inn file  $> Continue
                Alias a            -> alias a            $> Continue
                TryAlias name      -> tryAlias name printFn
                LoadScript file    -> loadScript file    $> Continue
                ProofStatus        -> proofStatus        $> Continue
                Log s t            -> handleLog (s,t)    $> Continue
                Exit               -> exit
    (output, shouldContinue) <- evaluateCommand command
    liftIO $ printFn output
    case shouldContinue of
        Continue -> pure Continue
        SuccessStop -> liftIO exitSuccess
        FailStop -> liftIO . exitWith $ ExitFailure 2
  where
    -- Extracts the Writer out of the RWST monad using the current state
    -- and updates the state, returning the writer output along with the
    -- monadic result.
    evaluateCommand
        :: ReplM claim ReplStatus
        -> StateT (ReplState claim) Simplifier (String, ReplStatus)
    evaluateCommand c = do
        st <- get
        (ext, st', w) <- Monad.Trans.lift $ runRWST c () st
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

showUsage :: MonadWriter String m => m ()
showUsage = putStrLn' showUsageMessage

exit
    :: Claim claim
    => ReplM claim ReplStatus
exit = do
    proofs <- allProofs
    ofile <- Lens.use lensOutputFile
    let fileName =
            maybe (error "Output file not specified") id (unOutputFile ofile)
    graphs <- Lens.use lensGraphs
    claims <- Lens.use lensClaims
    let patts =
            inProgressClaims graphs claims
            <> notStartedClaims graphs claims
        pattSort =
            termLikeSort
            . Rule.onePathRuleToPattern
            . Rule.OnePathRule
            . coerce
            $ claims !! 0
        conj = foldr TermLike.mkAnd (TermLike.mkTop pattSort) patts
    liftIO $ writeFile fileName (unparseToString conj)
    if isCompleted (Map.elems proofs)
       then return SuccessStop
       else return FailStop
  where
    inProgressClaims
        :: Claim claim
        => Map.Map ClaimIndex ExecutionGraph
        -> [claim]
        -> [TermLike.TermLike Variable]
    inProgressClaims gphs cls =
        Rule.onePathRuleToPattern
        . createReachabilityClaim
        <$> terminalAndParentClaims gphs cls
    terminalAndParentClaims
        :: Claim claim
        => Map.Map ClaimIndex ExecutionGraph
        -> [claim]
        -> [(claim, CommonStrategyPattern)]
    terminalAndParentClaims gphs cls =
        let pairs =
                ( \(x, y) -> ([x], y) )
                <$> (Map.toList . terminalPatterns) gphs
        in fmap
            ( \(x, y) -> (cls !! (unClaimIndex x), y) )
            (pairs >>= uncurry zip)
    notStartedClaims
        :: Claim claim
        => Map.Map ClaimIndex ExecutionGraph
        -> [claim]
        -> [TermLike.TermLike Variable]
    notStartedClaims gphs cls =
        Rule.onePathRuleToPattern
        . Rule.OnePathRule
        . coerce
        . (cls !!)
        . unClaimIndex
        <$> (Set.toList $ Set.difference
                (Set.fromList $ fmap ClaimIndex [0..length cls - 1])
                (Set.fromList $ Map.keys gphs))
    createReachabilityClaim
        :: Claim claim
        => (claim, CommonStrategyPattern)
        -> Rule.OnePathRule Variable
    createReachabilityClaim (cl, cpatt) =
        Rule.OnePathRule
        $ Rule.RulePattern
            { left = pattToLeftPatt cpatt
            , right = claimToRightPatt cl
            , requires = Predicate.makeTruePredicate
            , ensures = claimToEnsures cl
            , attributes = Default.def
            }
    pattToLeftPatt
        :: CommonStrategyPattern
        -> TermLike Variable
    pattToLeftPatt =
        toTermLike . fromJust . extractUnproven
    claimToRightPatt
        :: Claim claim
        => claim
        -> TermLike Variable
    claimToRightPatt =
        Rule.right . coerce
    claimToEnsures
        :: Claim claim
        => claim
        -> Predicate.Predicate Variable
    claimToEnsures =
        Rule.ensures . coerce
    terminalPatterns
        :: Map.Map ClaimIndex ExecutionGraph
        -> Map.Map ClaimIndex [CommonStrategyPattern]
    terminalPatterns gphs =
        terminalPattern
        . graphWithLeafs
        . Strategy.graph
        <$> gphs
    graphWithLeafs :: InnerGraph -> (InnerGraph, [Graph.Node])
    graphWithLeafs gph =
        (gph, join . Map.elems $ sortLeafsByType gph)
    terminalPattern
        :: (InnerGraph, [Graph.Node])
        -> [CommonStrategyPattern]
    terminalPattern (g, ns) =
        fmap (Graph.lab' . Graph.context g) ns
    isCompleted :: [GraphProofStatus] -> Bool
    isCompleted xs =
        foldr
            (&&)
            True
            (fmap (\x -> x == Completed || x == TrustedClaim) xs)

help :: MonadWriter String m => m ()
help = putStrLn' helpText

-- | Prints a claim using an index in the claims list.
showClaim
    :: Claim claim
    => MonadState (ReplState claim) m
    => MonadWriter String m
    => Maybe ClaimIndex
    -> m ()
showClaim =
    \case
        Nothing -> do
            currentCindex <- Lens.use lensClaimIndex
            putStrLn' . showCurrentClaimIndex $ currentCindex
        Just cindex -> do
            claim <- getClaimByIndex . unClaimIndex $ cindex
            maybe printNotFound (putStrLn' . showRewriteRule) $ claim

-- | Prints an axiom using an index in the axioms list.
showAxiom
    :: MonadState (ReplState claim) m
    => MonadWriter String m
    => AxiomIndex
    -- ^ index in the axioms list
    -> m ()
showAxiom aindex = do
    axiom <- getAxiomByIndex . unAxiomIndex $ aindex
    maybe printNotFound (putStrLn' . showRewriteRule)  $ axiom

-- | Changes the currently focused proof, using an index in the claims list.
prove
    :: forall claim m
    .  Claim claim
    => MonadState (ReplState claim) m
    => MonadWriter String m
    => ClaimIndex
    -- ^ index in the claims list
    -> m ()
prove cindex = do
    claim' <- getClaimByIndex . unClaimIndex $ cindex
    maybe printNotFound (startProving cindex) claim'
  where
    startProving :: ClaimIndex -> claim -> m ()
    startProving ci claim = do
        if isTrusted claim
            then putStrLn'
                    $ "Cannot switch to proving claim "
                    <> show (unClaimIndex ci)
                    <> ". Claim is trusted."
            else do
                switchToProof claim ci
                putStrLn'
                    $ "Switched to proving claim "
                    <> show (unClaimIndex ci)

showGraph
    :: MonadIO m
    => MonadWriter String m
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
    => Natural
    -- ^ maximum number of steps to perform
    -> ReplM claim ()
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
    => Natural
    -- ^ maximum number of steps to perform
    -> ReplM claim ()
proveStepsF n = do
    graph  <- getExecutionGraph
    node   <- Lens.use lensNode
    graph' <- recursiveForcedStep n graph node
    updateExecutionGraph graph'

-- | Loads a script from a file.
loadScript
    :: forall claim
    .  Claim claim
    => FilePath
    -- ^ path to file
    -> ReplM claim ()
loadScript file = do
    state <- get
    mstate <- lift $ parseEvalScript state file
    put $ maybe state id mstate

handleLog
    :: MonadState (ReplState claim) m
    => (Logger.Severity, LogType)
    -> m ()
handleLog t = lensLogging .= t

-- | Focuses the node with id equals to 'n'.
selectNode
    :: MonadState (ReplState claim) m
    => Claim claim
    => MonadWriter String m
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
    => Maybe ReplNode
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim ()
showConfig configNode = do
    maybeConfig <- getConfigAt configNode
    case maybeConfig of
        Nothing -> putStrLn' "Invalid node!"
        Just (ReplNode node, config) -> do
            omit <- Lens.use lensOmit
            putStrLn' $ "Config at node " <> show node <> " is:"
            putStrLn' $ unparseStrategy omit config

-- | Shows current omit list if passed 'Nothing'. Adds/removes from the list
-- depending on whether the string already exists in the list or not.
omitCell
    :: forall claim
    .  Maybe String
    -- ^ Nothing to show current list, @Just str@ to add/remove to list
    -> ReplM claim ()
omitCell =
    \case
        Nothing  -> showCells
        Just str -> addOrRemove str
  where
    showCells :: ReplM claim ()
    showCells = do
        omitList <- Lens.use lensOmit
        case omitList of
            [] -> putStrLn' "Omit list is currently empty."
            _  -> traverse_ putStrLn' omitList

    addOrRemove :: String -> ReplM claim ()
    addOrRemove str = lensOmit %= toggle str

    toggle :: String -> [String] -> [String]
    toggle x xs
      | x `elem` xs = filter (/= x) xs
      | otherwise   = x : xs

-- | Shows all leaf nodes identifiers which are either stuck or can be
-- evaluated further.
showLeafs
    :: forall claim
    . Claim claim
    => ReplM claim ()
showLeafs = do
    leafsByType <- sortLeafsByType <$> getInnerGraph
    case Map.foldMapWithKey showPair leafsByType of
        "" -> putStrLn' "No leafs found, proof is complete."
        xs -> putStrLn' xs
  where
    showPair :: NodeState -> [Graph.Node] -> String
    showPair ns xs = show ns <> ": " <> show xs

proofStatus
    :: forall claim
    .  Claim claim
    => ReplM claim ()
proofStatus = do
    proofs <- allProofs
    putStrLn' . showProofStatus $ proofs

allProofs
    :: forall claim
    .  Claim claim
    => ReplM claim (Map.Map ClaimIndex GraphProofStatus)
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
    => MonadWriter String m
    => Claim claim
    => Maybe ReplNode
    -> m ()
showRule configNode = do
    maybeRule <- getRuleFor configNode
    case maybeRule of
        Nothing -> putStrLn' "Invalid node!"
        Just rule -> do
            axioms <- Lens.use lensAxioms
            putStrLn' $ showRewriteRule rule
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
    => Maybe ReplNode
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim ()
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
    => Maybe ReplNode
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim ()
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
    => MonadWriter String m
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
    => MonadWriter String m
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
    => MonadWriter String m
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

-- | Redirect command to specified file.
redirect
    :: forall claim
    .  Claim claim
    => ReplCommand
    -- ^ command to redirect
    -> FilePath
    -- ^ file path
    -> ReplM claim ()
redirect cmd path = do
    get >>= runInterpreter >>= put
    putStrLn' "File created."
  where
    redirectToFile :: String -> IO ()
    redirectToFile = writeFile path

    runInterpreter
        :: ReplState claim
        -> ReplM claim (ReplState claim)
    runInterpreter = lift . execStateT (replInterpreter redirectToFile cmd)

-- | Attempt to use a specific axiom or claim to progress the current proof.
tryAxiomClaim
    :: forall claim
    .  Claim claim
    => Either AxiomIndex ClaimIndex
    -- ^ tagged index in the axioms or claims list
    -> ReplM claim ()
tryAxiomClaim eac = do
    maybeAxiomOrClaim <- getAxiomOrClaimByIndex eac
    case maybeAxiomOrClaim of
        Nothing -> putStrLn' "Could not find axiom or claim."
        Just axiomOrClaim -> do
            node <- Lens.use lensNode
            (graph, stepResult) <- runStepper'
                (rightToList axiomOrClaim)
                (leftToList  axiomOrClaim)
                node
            case stepResult of
                NoResult ->
                    showUnificationFailure axiomOrClaim node
                SingleResult node' -> do
                    lensNode .= node'
                    updateExecutionGraph graph
                    putStrLn' "Unification successful."
                BranchResult nodes -> do
                    stuckToUnstuck nodes graph
                    putStrLn'
                        $ "Unification successful with branching: "
                            <> show nodes
  where
    leftToList :: Either a b -> [a]
    leftToList = either pure (const [])

    rightToList :: Either a b -> [b]
    rightToList = either (const []) pure

    stuckToUnstuck :: [ReplNode] -> ExecutionGraph -> ReplM claim ()
    stuckToUnstuck nodes Strategy.ExecutionGraph{ graph } =
        updateInnerGraph
        $ Graph.gmap (stuckToRewrite
        $ fmap unReplNode nodes) graph

    stuckToRewrite xs ct@(to, n, lab, from)
        | n `elem` xs =
            case lab of
                Stuck patt -> (to, n, RewritePattern patt, from)
                _ -> ct
        | otherwise = ct

    showUnificationFailure
        :: Either (Axiom) claim
        -> ReplNode
        -> ReplM claim ()
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
    runUnifier' first second =
        runUnifier first second >>= putStrLn' . formatUnificationMessage

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
    => MonadWriter String m
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
    :: MonadState (ReplState claim) m
    => MonadWriter String m
    => MonadIO m
    => FilePath
    -- ^ path to file
    -> m ()
saveSession path = do
   content <- seqUnlines <$> Lens.use lensCommands
   liftIO $ writeFile path content
   putStrLn' "Done."
 where
   seqUnlines :: Seq String -> String
   seqUnlines = unlines . toList

-- | Pipe result of command to specified program.
pipe
    :: forall claim
    .  Claim claim
    => ReplCommand
    -- ^ command to pipe
    -> String
    -- ^ path to the program that will receive the command's output
    -> [String]
    -- ^ additional arguments to be passed to the program
    -> ReplM claim ()
pipe cmd file args = do
    exists <- liftIO $ findExecutable file
    case exists of
        Nothing -> putStrLn' "Cannot find executable."
        Just exec -> do
            (maybeInput, maybeOutput, _, _) <- createProcess' exec
            let
                outputFunc = maybe putStrLn hPutStr maybeInput
            get >>= runInterpreter outputFunc >>= put
            case maybeOutput of
                Nothing ->
                    putStrLn' "Error: couldn't access output handle."
                Just handle -> do
                    output <- liftIO $ hGetContents handle
                    putStrLn' output
  where
    runInterpreter
        :: (String -> IO ())
        -> ReplState claim
        -> ReplM claim (ReplState claim)
    runInterpreter io = lift . execStateT (replInterpreter io cmd)

    createProcess' exec =
        liftIO $ createProcess (proc exec args)
            { std_in = CreatePipe, std_out = CreatePipe }

-- | Appends output of a command to a file.
appendTo
    :: forall claim
    .  Claim claim
    => ReplCommand
    -- ^ command
    -> FilePath
    -- ^ file to append to
    -> ReplM claim ()
appendTo cmd file = do
    get >>= runInterpreter >>= put
    putStrLn' $ "Appended output to \"" <> file <> "\"."
  where
    runInterpreter
        :: ReplState claim
        -> ReplM claim (ReplState claim)
    runInterpreter = lift . execStateT (replInterpreter (appendFile file) cmd)

alias
    :: forall m claim
    .  MonadState (ReplState claim) m
    => MonadWriter String m
    => AliasDefinition
    -> m ()
alias a = do
    result <- runExceptT $ addOrUpdateAlias a
    case result of
        Left err -> putStrLn' $ showAliasError err
        Right _  -> pure ()

tryAlias
    :: forall claim
    .  Claim claim
    => ReplAlias
    -> (String -> IO ())
    -> ReplM claim ReplStatus
tryAlias replAlias@ReplAlias { name } printFn = do
    res <- findAlias name
    case res of
        Nothing  -> showUsage $> Continue
        Just aliasDef -> do
            let
                command = substituteAlias aliasDef replAlias
                parsedCommand =
                    maybe ShowUsage id $ parseMaybe commandParser command
            (cont, st') <- get >>= runInterpreter parsedCommand
            put st'
            return cont
  where
    runInterpreter
        :: ReplCommand
        -> ReplState claim
        -> ReplM claim (ReplStatus, ReplState claim)
    runInterpreter cmd =
        lift . runStateT (replInterpreter printFn cmd)

-- | Performs n proof steps, picking the next node unless branching occurs.
-- Returns 'Left' while it has to continue looping, and 'Right' when done
-- or when execution branches or proof finishes earlier than the counter.
--
-- See 'loopM' for details.
performStepNoBranching
    :: forall claim
    .  Claim claim
    => (Natural, StepResult)
    -- ^ (current step, last result)
    -> ReplM claim (Either (Natural, StepResult) (Natural, StepResult))
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
    => Natural
    -> ExecutionGraph
    -> ReplNode
    -> ReplM claim ExecutionGraph
recursiveForcedStep n graph node
  | n == 0    = return graph
  | otherwise = do
      ReplState { claims , axioms , claim , stepper } <- get
      graph'@Strategy.ExecutionGraph { graph = gr } <-
          lift $ stepper claim claims axioms graph node
      case Graph.suc gr (unReplNode node) of
          [] -> return graph'
          xs -> foldM (recursiveForcedStep $ n-1) graph' (fmap ReplNode xs)

-- | Display a rule as a String.
showRewriteRule
    :: Coercible (RewriteRule Variable) rule
    => rule
    -> String
showRewriteRule rule =
    unparseToString rule'
    <> "\n"
    <> (show . Pretty.pretty . extractSourceAndLocation $ rule')
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
    :: [String]
    -- ^ omit list
    -> CommonStrategyPattern
    -- ^ pattern
    -> String
unparseStrategy omitList =
    strategyPattern StrategyPatternTransformer
        { rewriteTransformer = \pat -> unparseToString (hide <$> pat)
        , stuckTransformer =
            \pat -> "Stuck: \n" <> unparseToString (hide <$> pat)
        , bottomValue = "Reached bottom"
        }
  where
    hide :: TermLike Variable -> TermLike Variable
    hide =
        Recursive.unfold $ \termLike ->
            case Recursive.project termLike of
                ann :< TermLike.ApplicationF app
                  | shouldBeExcluded (applicationSymbolOrAlias app) ->
                    -- Do not display children
                    ann :< TermLike.ApplicationF (withoutChildren app)
                projected -> projected

    withoutChildren app = app { applicationChildren = [] }

    shouldBeExcluded =
       (`elem` omitList)
           . Text.unpack
           . Id.getId
           . symbolOrAliasConstructor

putStrLn' :: MonadWriter String m => String -> m ()
putStrLn' str = tell $ str <> "\n"

printIfNotEmpty :: String -> IO ()
printIfNotEmpty =
    \case
        "" -> pure ()
        xs -> putStrLn xs

printNotFound :: MonadWriter String m => m ()
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
    void
    . Graph.runGraphviz
        (Graph.graphToDot (graphParams len) gr) Graph.Jpeg
    $ file <> ".jpeg"

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
                maybe "Unknown" Text.Lazy.pack
                    . showAxiomOrClaim ln
                    . Attribute.identifier
                    . Rule.attributes
                    . Rule.getRewriteRule
                    $ rule

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

parseEvalScript
    :: forall claim
    .  Claim claim
    => ReplState claim
    -> FilePath
    -> Simplifier (Maybe (ReplState claim))
parseEvalScript state file = do
    exists <- liftIO . doesFileExist $ file
    if exists == True
        then do
            contents <- liftIO $ readFile file
            let result = runParser scriptParser file contents
            either parseFailed (executeScript state) result
        else do
            liftIO . putStrLn
                $ "Cannot find " <> file
            return Nothing

  where

    parseFailed
        :: ParseErrorBundle String String
        -> Simplifier (Maybe (ReplState claim))
    parseFailed err = do
        liftIO . putStrLn
            $ "\nCouldn't parse initial script file."
            <> "\nParser error at: "
            <> errorBundlePretty err
        return Nothing

    executeScript
        :: ReplState claim
        -> [ReplCommand]
        -> Simplifier (Maybe (ReplState claim))
    executeScript st cmds = do
        newSt <- execStateT (traverse_ (replInterpreter $ \_ -> return () ) cmds) st
        return . return $ newSt

formatUnificationMessage :: Maybe (Pretty.Doc ()) -> String
formatUnificationMessage =
    maybe "No unification error found." show

findLeafNodes :: InnerGraph -> [Graph.Node]
findLeafNodes graph =
    filter ((==) 0 . Graph.outdeg graph) $ Graph.nodes graph

sortLeafsByType :: InnerGraph -> Map.Map NodeState [Graph.Node]
sortLeafsByType graph =
    Map.fromList
        . groupSort
        . catMaybes
        . fmap (getNodeState graph)
        . findLeafNodes
        $ graph

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
