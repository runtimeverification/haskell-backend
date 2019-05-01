{-|
Module      : Kore.Interpreter
Description : REPL interpreter
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl.Interpreter
    ( replInterpreter
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import           Control.Lens
                 ( (%=), (.=) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad
                 ( foldM )
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
import           Data.Coerce
                 ( coerce )
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
                 ( catMaybes, listToMaybe )
import           Data.Sequence
                 ( Seq )
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Exts
                 ( toList )
import           GHC.IO.Handle
                 ( hGetContents, hPutStr )
import           System.Directory
                 ( findExecutable )
import           System.Process
                 ( StdStream (CreatePipe), createProcess, proc, std_in,
                 std_out )

import           Kore.AST.Common
                 ( Pattern (..) )
import           Kore.AST.MetaOrObject
import           Kore.Attribute.Axiom
                 ( SourceLocation (..) )
import qualified Kore.Attribute.Axiom as Attribute
                 ( Axiom (..), RuleIndex (..), sourceLocation )
import           Kore.Attribute.RuleIndex
import           Kore.OnePath.Step
                 ( CommonStrategyPattern, StrategyPattern (..),
                 StrategyPatternTransformer (StrategyPatternTransformer),
                 strategyPattern )
import qualified Kore.OnePath.Step as StrategyPatternTransformer
                 ( StrategyPatternTransformer (..) )
import           Kore.OnePath.Verification
                 ( Axiom (..) )
import           Kore.OnePath.Verification
                 ( Claim )
import           Kore.Repl.Data
import           Kore.Step.Pattern
                 ( Conditional (..) )
import           Kore.Step.Rule
                 ( RewriteRule (..), RulePattern (..) )
import qualified Kore.Step.Rule as Rule
import qualified Kore.Step.Rule as Axiom
                 ( attributes )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Step.TermLike
                 ( TermLike )
import           Kore.Syntax.Application
import qualified Kore.Syntax.Id as Id
                 ( Id (..) )
import           Kore.Syntax.Variable
                 ( Variable )
import           Kore.Unparser
                 ( unparseToString )

-- | Warning: you should never use WriterT or RWST. It is used here with
-- _great care_ of evaluating the RWST to a StateT immediatly, and thus getting
-- rid of the WriterT part of the stack. This happens in the implementation of
-- 'replInterpreter'.
type ReplM claim level a = RWST () String (ReplState claim level) Simplifier a

-- | Interprets a REPL command in a stateful Simplifier context.
replInterpreter
    :: forall claim
    .  Claim claim
    => (String -> IO ())
    -> ReplCommand
    -> StateT (ReplState claim Object) Simplifier Bool
replInterpreter printFn replCmd = do
    let command = case replCmd of
                ShowUsage          -> showUsage          $> True
                Help               -> help               $> True
                ShowClaim c        -> showClaim c        $> True
                ShowAxiom a        -> showAxiom a        $> True
                Prove i            -> prove i            $> True
                ShowGraph          -> showGraph          $> True
                ProveSteps n       -> proveSteps n       $> True
                ProveStepsF n      -> proveStepsF n      $> True
                SelectNode i       -> selectNode i       $> True
                ShowConfig mc      -> showConfig mc      $> True
                OmitCell c         -> omitCell c         $> True
                ShowLeafs          -> showLeafs          $> True
                ShowRule   mc      -> showRule mc        $> True
                ShowPrecBranch mn  -> showPrecBranch mn  $> True
                ShowChildren mn    -> showChildren mn    $> True
                Label ms           -> label ms           $> True
                LabelAdd l mn      -> labelAdd l mn      $> True
                LabelDel l         -> labelDel l         $> True
                Redirect inn file  -> redirect inn file  $> True
                Try ac             -> tryAxiomClaim ac   $> True
                Clear n            -> clear n            $> True
                SaveSession file   -> saveSession file   $> True
                Pipe inn file args -> pipe inn file args $> True
                AppendTo inn file  -> appendTo inn file  $> True
                Exit               -> pure                  False
    (output, shouldContinue) <- evaluateCommand command
    liftIO $ printFn output
    pure shouldContinue
  where
    -- Extracts the Writer out of the RWST monad using the current state
    -- and updates the state, returning the writer output along with the
    -- monadic result.
    evaluateCommand
        :: ReplM claim level Bool
        -> StateT (ReplState claim level) Simplifier (String, Bool)
    evaluateCommand c = do
        st <- get
        (exit, st', w) <- Monad.Trans.lift $ runRWST c () st
        put st'
        pure (w, exit)

showUsage :: MonadWriter String m => m ()
showUsage = putStrLn' "Could not parse command, try using 'help'."

help :: MonadWriter String m => m ()
help = putStrLn' helpText

-- | Prints a claim using an index in the claims list.
showClaim
    :: Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Int
    -- ^ index in the claims list
    -> m ()
showClaim index = do
    claim <- getClaimByIndex index
    maybe printNotFound (printRewriteRule .RewriteRule . coerce) $ claim

-- | Prints an axiom using an index in the axioms list.
showAxiom
    :: MonadState (ReplState claim level) m
    => MonadWriter String m
    => Int
    -- ^ index in the axioms list
    -> m ()
showAxiom index = do
    axiom <- getAxiomByIndex index
    maybe printNotFound (printRewriteRule . unAxiom) $ axiom

-- | Changes the currently focused proof, using an index in the claims list.
prove
    :: forall level claim m
    .  Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Int
    -- ^ index in the claims list
    -> m ()
prove index = do
    claim' <- getClaimByIndex index
    maybe printNotFound initProof claim'
  where
    initProof :: claim -> m ()
    initProof claim = do
            initializeProofFor claim
            putStrLn' "Execution Graph initiated"

showGraph
    :: MonadIO m
    => MonadState (ReplState claim level) m
    => m ()
showGraph = do
    graph <- getInnerGraph
    axioms <- Lens.use lensAxioms
    liftIO $ showDotGraph (length axioms) graph

-- | Executes 'n' prove steps, or until branching occurs.
proveSteps
    :: Claim claim
    => Int
    -- ^ maximum number of steps to perform
    -> ReplM claim level ()
proveSteps n = do
    result <- loopM performStepNoBranching (n, SingleResult n)
    case result of
        (0, SingleResult _) -> pure ()
        (done, res) ->
            putStrLn'
                $ "Stopped after "
                <> show (n - done - 1)
                <> " step(s) due to "
                <> show res

-- | Executes 'n' prove steps, distributing over branches. It will perform less
-- than 'n' steps if the proof is stuck or completed in less than 'n' steps.
proveStepsF
    :: Claim claim
    => Int
    -- ^ maximum number of steps to perform
    -> ReplM claim level ()
proveStepsF n = do
    graph  <- Lens.use lensGraph
    node   <- Lens.use lensNode
    graph' <- recursiveForcedStep n graph node
    lensGraph .= graph'

-- | Focuses the node with id equals to 'n'.
selectNode
    :: MonadState (ReplState claim level) m
    => MonadWriter String m
    => Int
    -- ^ node identifier
    -> m ()
selectNode i = do
    graph <- getInnerGraph
    if i `elem` Graph.nodes graph
        then lensNode .= i
        else putStrLn' "Invalid node!"

-- | Shows configuration at node 'n', or current node if 'Nothing' is passed.
showConfig
    :: level ~ Object
    => Maybe Int
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim level ()
showConfig configNode = do
    maybeConfig <- getConfigAt configNode
    case maybeConfig of
        Nothing -> putStrLn' "Invalid node!"
        Just (node, config) -> do
            omit <- Lens.use lensOmit
            putStrLn' $ "Config at node " <> show node <> " is:"
            putStrLn' $ unparseStrategy omit config

-- | Shows current omit list if passed 'Nothing'. Adds/removes from the list
-- depending on whether the string already exists in the list or not.
omitCell
    :: forall claim level
    .  Maybe String
    -- ^ Nothing to show current list, @Just str@ to add/remove to list
    -> ReplM claim level ()
omitCell =
    \case
        Nothing  -> showCells
        Just str -> addOrRemove str
  where
    showCells :: ReplM claim level ()
    showCells = do
        omitList <- Lens.use lensOmit
        case omitList of
            [] -> putStrLn' "Omit list is currently empty."
            _  -> traverse_ putStrLn' omitList

    addOrRemove :: String -> ReplM claim level ()
    addOrRemove str = lensOmit %= toggle str

    toggle :: String -> [String] -> [String]
    toggle x xs
      | x `elem` xs = filter (/= x) xs
      | otherwise   = x : xs

-- | Shows all leaf nodes identifiers which are either stuck or can be
-- evaluated further.
showLeafs :: forall claim level. ReplM claim level ()
showLeafs = do
    leafsByType <- sortLeafsByType <$> getInnerGraph
    case foldMap showPair leafsByType of
        "" -> putStrLn' "No leafs found, proof is complete."
        xs -> putStrLn' xs
  where
    sortLeafsByType :: InnerGraph -> [(NodeState, [Graph.Node])]
    sortLeafsByType graph =
        groupSort
            . catMaybes
            . fmap (getNodeState graph)
            . findLeafNodes
            $ graph

    findLeafNodes :: InnerGraph -> [Graph.Node]
    findLeafNodes graph =
        filter ((==) 0 . Graph.outdeg graph) $ Graph.nodes graph

    getNodeState :: InnerGraph -> Graph.Node -> Maybe (NodeState, Graph.Node)
    getNodeState graph node =
        fmap (\nodeState -> (nodeState, node))
        . strategyPattern StrategyPatternTransformer
            { rewriteTransformer = const . Just $ UnevaluatedNode
            , stuckTransformer = const . Just $ StuckNode
            , bottomValue = Nothing
            }
        . Graph.lab'
        . Graph.context graph
        $ node

    showPair :: (NodeState, [Graph.Node]) -> String
    showPair (ns, xs) = show ns <> ": " <> show xs

showRule
    :: MonadState (ReplState claim level) m
    => MonadWriter String m
    => Maybe Int
    -> m ()
showRule configNode = do
    maybeRule <- getRuleFor configNode
    case maybeRule of
        Nothing -> putStrLn' "Invalid node!"
        Just rule -> do
            axioms <- Lens.use lensAxioms
            printRewriteRule rule
            let ruleIndex = getRuleIndex rule
            putStrLn' $ maybe
                "Error: identifier attribute wasn't initialized."
                id
                (showAxiomOrClaim (length axioms) ruleIndex)
  where
    getRuleIndex :: RewriteRule Object Variable -> Attribute.RuleIndex
    getRuleIndex = Attribute.identifier . Rule.attributes . Rule.getRewriteRule

-- | Shows the previous branching point.
showPrecBranch
    :: Maybe Int
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim level ()
showPrecBranch maybeNode = do
    graph <- getInnerGraph
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> putStrLn' "Invalid node!"
        Just node -> putStrLn' . show $ loop (loopCond graph) node
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
    :: Maybe Int
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> ReplM claim level ()
showChildren maybeNode = do
    graph <- getInnerGraph
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> putStrLn' "Invalid node!"
        Just node -> putStrLn' . show . Graph.suc graph $ node

-- | Shows existing labels or go to an existing label.
label
    :: forall level m claim
    .  MonadState (ReplState claim level) m
    => MonadWriter String m
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
        labels <- Lens.use lensLabels
        if null labels
           then putStrLn' "No labels are set."
           else putStrLn' $ Map.foldrWithKey acc "Labels: " labels

    gotoLabel :: String -> m ()
    gotoLabel l = do
        labels <- Lens.use lensLabels
        selectNode $ maybe (-1) id (Map.lookup l labels)

    acc :: String -> Graph.Node -> String -> String
    acc key node res =
        res <> "\n  " <> key <> ": " <> show node

-- | Adds label for selected node.
labelAdd
    :: MonadState (ReplState claim level) m
    => MonadWriter String m
    => String
    -- ^ label
    -> Maybe Int
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> m ()
labelAdd lbl maybeNode = do
    node' <- getTargetNode maybeNode
    case node' of
        Nothing -> putStrLn' "Target node is not in the graph."
        Just node -> do
            labels <- Lens.use lensLabels
            if lbl `Map.notMember` labels
                then do
                    lensLabels .= Map.insert lbl node labels
                    putStrLn' "Label added."
                else
                    putStrLn' "Label already exists."

-- | Removes a label.
labelDel
    :: MonadState (ReplState claim level) m
    => MonadWriter String m
    => String
    -- ^ label
    -> m ()
labelDel lbl = do
    labels <- Lens.use lensLabels
    if lbl `Map.member` labels
       then do
           lensLabels .= Map.delete lbl labels
           putStrLn' "Removed label."
       else
           putStrLn' "Label doesn't exist."

-- | Redirect command to specified file.
redirect
    :: forall level claim
    .  level ~ Object
    => Claim claim
    => ReplCommand
    -- ^ command to redirect
    -> FilePath
    -- ^ file path
    -> ReplM claim level ()
redirect cmd path = do
    get >>= runInterpreter >>= put
    putStrLn' "File created."
  where
    redirectToFile :: String -> IO ()
    redirectToFile = writeFile path

    runInterpreter
        :: ReplState claim level
        -> ReplM claim level (ReplState claim level)
    runInterpreter = lift . execStateT (replInterpreter redirectToFile cmd)

-- | Attempt to use a specific axiom or claim to progress the current proof.
tryAxiomClaim
    :: forall level claim
    .  level ~ Object
    => Claim claim
    => Either AxiomIndex ClaimIndex
    -- ^ tagged index in the axioms or claims list
    -> ReplM claim level ()
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
                    putStrLn' "Unification successful."
                BranchResult nodes -> do
                    stuckToUnstuck nodes graph
                    putStrLn'
                        $ "Unification successful with branching: " <> show nodes
  where
    leftToList :: Either a b -> [a]
    leftToList = either pure (const [])

    rightToList :: Either a b -> [b]
    rightToList = either (const []) pure

    stuckToUnstuck :: [Graph.Node] -> ExecutionGraph -> ReplM claim level ()
    stuckToUnstuck nodes Strategy.ExecutionGraph{ graph } =
        updateInnerGraph $ Graph.gmap (stuckToRewrite nodes) graph

    stuckToRewrite xs ct@(to, n, lab, from)
        | n `elem` xs =
            case lab of
                Stuck patt -> (to, n, RewritePattern patt, from)
                _ -> ct
        | otherwise = ct

    showUnificationFailure
        :: Either (Axiom level) claim
        -> Graph.Node
        -> ReplM claim level ()
    showUnificationFailure axiomOrClaim' node = do
        let first = extractLeftPattern axiomOrClaim'
        maybeSecond <- getConfigAt (Just node)
        case maybeSecond of
            Nothing -> putStrLn' "Unexpected error getting current config."
            Just (_, second) ->
                strategyPattern
                    StrategyPatternTransformer
                        { bottomValue        = putStrLn' "Cannot unify bottom"
                        , rewriteTransformer = unify first . term
                        , stuckTransformer   = unify first . term
                        }
                    second
    unify
        :: TermLike Variable
        -> TermLike Variable
        -> ReplM claim level ()
    unify first second = do
        unifier <- Lens.use lensUnifier
        mdoc <-
            Monad.Trans.lift . runUnifierWithExplanation $ unifier first second
        case mdoc of
            Nothing -> putStrLn' "No unification error found."
            Just doc -> putStrLn' $ show doc
    extractLeftPattern
        :: Either (Axiom level) claim
        -> TermLike Variable
    extractLeftPattern =
            left . getRewriteRule . either unAxiom coerce

-- | Removes specified node and all its child nodes.
clear
    :: forall level m claim
    .  MonadState (ReplState claim level) m
    => MonadWriter String m
    => Maybe Int
    -- ^ 'Nothing' for current node, or @Just n@ for a specific node identifier
    -> m ()
clear =
    \case
        Nothing -> Just <$> Lens.use lensNode >>= clear
        Just node
          | node == 0 -> putStrLn' "Cannot clear initial node (0)."
          | otherwise -> clear0 node
  where
    clear0 :: Int -> m ()
    clear0 node = do
        graph <- getInnerGraph
        let
            nodesToBeRemoved = collect (next graph) node
            graph' = Graph.delNodes nodesToBeRemoved graph
        updateInnerGraph graph'
        lensNode .= prevNode graph' node
        putStrLn' $ "Removed " <> show (length nodesToBeRemoved) <> " node(s)."

    next :: InnerGraph -> Graph.Node -> [Graph.Node]
    next gr n = fst <$> Graph.lsuc gr n

    collect :: (a -> [a]) -> a -> [a]
    collect f x = x : [ z | y <- f x, z <- collect f y]

    prevNode :: InnerGraph -> Graph.Node -> Graph.Node
    prevNode graph = maybe 0 id . listToMaybe . fmap fst . Graph.lpre graph

-- | Save this sessions' commands to the specified file.
saveSession
    :: MonadState (ReplState level claim) m
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
    :: forall level claim
    .  level ~ Object
    => Claim claim
    => ReplCommand
    -- ^ command to pipe
    -> String
    -- ^ path to the program that will receive the command's output
    -> [String]
    -- ^ additional arguments to be passed to the program
    -> ReplM claim level ()
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
        -> ReplState claim level
        -> ReplM claim level (ReplState claim level)
    runInterpreter io = lift . execStateT (replInterpreter io cmd)

    createProcess' exec =
        liftIO $ createProcess (proc exec args)
            { std_in = CreatePipe, std_out = CreatePipe }

-- | Appends output of a command to a file.
appendTo
    :: forall claim level
    .  level ~ Object
    => Claim claim
    => ReplCommand
    -- ^ command
    -> FilePath
    -- ^ file to append to
    -> ReplM claim level ()
appendTo cmd file = do
    get >>= runInterpreter >>= put
    putStrLn' $ "Appended output to \"" <> file <> "\"."
  where
    runInterpreter
        :: ReplState claim level
        -> ReplM claim level (ReplState claim level)
    runInterpreter = lift . execStateT (replInterpreter (appendFile file) cmd)


-- | Performs n proof steps, picking the next node unless branching occurs.
-- Returns 'Left' while it has to continue looping, and 'Right' when done
-- or when execution branches or proof finishes earlier than the counter.
--
-- See 'loopM' for details.
performStepNoBranching
    :: forall claim level
    .  Claim claim
    => (Int, StepResult)
    -- ^ (current step, last result)
    -> ReplM claim level (Either (Int, StepResult) (Int, StepResult))
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
    => Int
    -> ExecutionGraph
    -> Graph.Node
    -> ReplM claim level ExecutionGraph
recursiveForcedStep n graph node
  | n == 0    = return graph
  | otherwise = do
      ReplState { claims , axioms , claim , stepper } <- get
      graph'@Strategy.ExecutionGraph { graph = gr } <-
          lift $ stepper claim claims axioms graph node
      case (Graph.suc gr node) of
          [] -> return graph'
          xs -> foldM (recursiveForcedStep $ n-1) graph' xs

-- | Prints an unparsed rewrite rule along with its source location.
printRewriteRule :: MonadWriter String m => RewriteRule level Variable -> m ()
printRewriteRule rule = do
    putStrLn' $ unparseToString rule
    putStrLn'
        . show
        . Pretty.pretty
        . extractSourceAndLocation
        $ rule
  where
    extractSourceAndLocation
        :: RewriteRule level Variable
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
                ann :< ApplicationPattern app
                  | shouldBeExcluded (applicationSymbolOrAlias app) ->
                    -- Do not display children
                    ann :< ApplicationPattern (withoutChildren app)
                projected -> projected

    withoutChildren app = app { applicationChildren = [] }

    shouldBeExcluded =
       (`elem` omitList)
           . Text.unpack
           . Id.getId
           . symbolOrAliasConstructor

putStrLn' :: MonadWriter String m => String -> m ()
putStrLn' str = tell $ str <> "\n"

printNotFound :: MonadWriter String m => m ()
printNotFound = putStrLn' "Variable or index not found"

-- | Shows the 'dot' graph. This currently only works on Linux. The 'Int'
-- parameter is needed in order to distinguish between axioms and claims and
-- represents the number of available axioms.
showDotGraph :: Int -> InnerGraph -> IO ()
showDotGraph len =
    (flip Graph.runGraphvizCanvas') Graph.Xlib
        . Graph.graphToDot params
  where
    params = Graph.nonClusteredParams
        { Graph.fmtEdge = \(_, _, l) ->
            [Graph.textLabel (ruleIndex l)]
        }
    ruleIndex lbl =
        case listToMaybe . toList $ lbl of
            Nothing -> "Simpl/RD"
            Just rule ->
                maybe "Unknown" Text.Lazy.pack
                    . showAxiomOrClaim len
                    . Attribute.identifier
                    . Rule.attributes
                    . Rule.getRewriteRule
                    $ rule

showAxiomOrClaim :: Int -> Attribute.RuleIndex -> Maybe String
showAxiomOrClaim _   (RuleIndex Nothing) = Nothing
showAxiomOrClaim len (RuleIndex (Just rid))
  | rid < len = Just $ "Axiom " <> show rid
  | otherwise = Just $ "Claim " <> show (rid - len)

data NodeState = StuckNode | UnevaluatedNode
    deriving (Eq, Ord, Show)
