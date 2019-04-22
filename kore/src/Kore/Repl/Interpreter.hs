{-|
Module      : Kore.Interpreter
Description : REPL interpreter
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl.Interpreter
    ( replInterpreter
    , emptyExecutionGraph
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import           Control.Error.Safe
                 ( atZ )
import           Control.Lens
                 ( (%=), (.=) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad
                 ( foldM, join )
import           Control.Monad.Extra
                 ( loop, loopM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.RWS.Strict
                 ( MonadWriter, RWST, get, lift, runRWST, tell )
import           Control.Monad.State.Strict
                 ( MonadState, StateT (..), evalStateT )
import qualified Control.Monad.Trans.Class as Monad.Trans
import           Data.Bifunctor
                 ( bimap )
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

import           Kore.AST.Common
                 ( Application (..), Pattern (..), SymbolOrAlias (..),
                 Variable )
import qualified Kore.AST.Identifier as Identifier
                 ( Id (..) )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject, Object )
import           Kore.Attribute.Axiom
                 ( SourceLocation (..) )
import qualified Kore.Attribute.Axiom as Attribute
                 ( Axiom (..), sourceLocation )
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
                 ( StepPattern )
import           Kore.Step.Representation.ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.Rule
                 ( RewriteRule (..) )
import           Kore.Step.Rule
                 ( RulePattern (..) )
import qualified Kore.Step.Rule as Rule
import qualified Kore.Step.Rule as Axiom
                 ( attributes )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Unparser
                 ( unparseToString )

-- | Warning: you should never use WriterT or RWST. It is used here with
-- _great care_ of evaluating the RWST to a StateT immediatly, and thus getting
-- rid of the WriterT part of the stack. This happens in the implementation of
-- 'replInterpreter'.
type ReplM claim level a = RWST () String (ReplState claim level) Simplifier a

-- | Interprets a REPL command in a stateful Simplifier context.
replInterpreter
    :: forall level claim
    .  MetaOrObject level
    => Claim claim
    => (String -> IO ())
    -> ReplCommand
    -> StateT (ReplState claim level) Simplifier Bool
replInterpreter output cmd =
    StateT $ \st -> do
        let rwst = case cmd of
                    ShowUsage         -> showUsage         $> True
                    Help              -> help              $> True
                    ShowClaim c       -> showClaim c       $> True
                    ShowAxiom a       -> showAxiom a       $> True
                    Prove i           -> prove i           $> True
                    ShowGraph         -> showGraph         $> True
                    ProveSteps n      -> proveSteps n      $> True
                    ProveStepsF n     -> proveStepsF n     $> True
                    SelectNode i      -> selectNode i      $> True
                    ShowConfig mc     -> showConfig mc     $> True
                    OmitCell c        -> omitCell c        $> True
                    ShowLeafs         -> showLeafs         $> True
                    ShowRule   mc     -> showRule mc       $> True
                    ShowPrecBranch mn -> showPrecBranch mn $> True
                    ShowChildren mn   -> showChildren mn   $> True
                    Label ms          -> label ms          $> True
                    LabelAdd l mn     -> labelAdd l mn     $> True
                    LabelDel l        -> labelDel l        $> True
                    Redirect inn file -> redirect inn file $> True
                    Try ac            -> tryAxiomClaim ac  $> True
                    Clear n           -> clear n           $> True
                    SaveSession file  -> saveSession file  $> True
                    Exit              -> pure                 False
        (exit, st', w) <- runRWST rwst () st
        liftIO $ output w
        pure (exit, st')

showUsage :: MonadWriter String m => m ()
showUsage =
    putStrLn' "Could not parse command, try using 'help'."

help :: MonadWriter String m => m ()
help = putStrLn' helpText

showClaim
    :: MonadIO m
    => Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Int
    -> m ()
showClaim index = do
    claim <- Lens.preuse $ lensClaims . Lens.element index
    maybe printNotFound (printRewriteRule .RewriteRule . coerce) $ claim

showAxiom
    :: MonadIO m
    => Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Int
    -> m ()
showAxiom index = do
    axiom <- Lens.preuse $ lensAxioms . Lens.element index
    maybe printNotFound (printRewriteRule . unAxiom) $ axiom

prove
    :: (level ~ Object)
    => MonadIO m
    => Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Int
    -> m ()
prove index = do
    claim' <- Lens.preuse $ lensClaims . Lens.element index
    case claim' of
        Nothing -> printNotFound
        Just claim -> do
            let
                graph@Strategy.ExecutionGraph { root }
                    = emptyExecutionGraph claim
            lensGraph  .= graph
            lensClaim  .= claim
            lensNode   .= root
            lensLabels .= Map.empty
            putStrLn' "Execution Graph initiated"

showGraph
    :: MonadIO m
    => Claim claim
    => MonadState (ReplState claim level) m
    => m ()
showGraph = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    axioms <- Lens.use lensAxioms
    liftIO $ showDotGraph (length axioms) graph

proveSteps :: Claim claim => Int -> ReplM claim level ()
proveSteps n = do
    result <- loopM performStepNoBranching (n, Success)
    case result of
        (0, Success) -> pure ()
        (done, res) ->
            putStrLn'
                $ "Stopped after "
                <> show (n - done - 1)
                <> " step(s) due to "
                <> show res

proveStepsF :: Claim claim => Int -> ReplM claim level ()
proveStepsF n = do
    graph  <- Lens.use lensGraph
    node   <- Lens.use lensNode
    graph' <- recursiveForcedStep n graph node
    lensGraph .= graph'
    lensNode  .= (snd $ Graph.nodeRange . Strategy.graph $ graph')

selectNode
    :: Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Int
    -> m ()
selectNode i = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    if i `elem` Graph.nodes graph
        then lensNode .= i
        else putStrLn' "Invalid node!"

showConfig
    :: MetaOrObject level
    => Claim claim
    => Maybe Int
    -> ReplM claim level ()
showConfig configNode = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    node <- Lens.use lensNode
    let node' = maybe node id configNode
    if node' `elem` Graph.nodes graph
        then do
            omit <- Lens.use lensOmit
            putStrLn' $ "Config at node " <> show node' <> " is:"
            putStrLn'
                . unparseStrategy omit
                . Graph.lab'
                . Graph.context graph
                $ node'
        else putStrLn' "Invalid node!"

omitCell :: Claim claim => Maybe String -> ReplM claim level ()
omitCell =
    \case
        Nothing  -> showCells
        Just str -> addOrRemove str
  where
    showCells :: ReplM claim level ()
    showCells = Lens.use lensOmit >>= traverse_ putStrLn'

    addOrRemove :: String -> ReplM claim level ()
    addOrRemove str = lensOmit %= toggle str

    toggle :: String -> [String] -> [String]
    toggle x xs
      | x `elem` xs = filter (/= x) xs
      | otherwise   = x : xs

data NodeStates = StuckNode | UnevaluatedNode
    deriving (Eq, Ord, Show)

showLeafs
    :: MetaOrObject level
    => Claim claim
    => ReplM claim level ()
showLeafs = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    let nodes = Graph.nodes graph
    let leafs = filter (\x -> (Graph.outdeg graph x) == 0) nodes
    let result =
            groupSort
                . catMaybes
                . fmap (getNodeState graph)
                $ leafs

    case foldr ((<>) . showPair) "" result of
        "" -> putStrLn' "No leafs found, proof is complete"
        xs -> putStrLn' xs
  where
    getNodeState graph node =
        maybe Nothing (\x -> Just (x, node))
        . strategyPattern StrategyPatternTransformer
            { rewriteTransformer = const . Just $ UnevaluatedNode
            , stuckTransformer = const . Just $ StuckNode
            , bottomValue = Nothing
            }
        . Graph.lab'
        . Graph.context graph
        $ node

    showPair :: (NodeStates, [Graph.Node]) -> String
    showPair (ns, xs) = show ns <> ": " <> show xs

showRule
    :: MetaOrObject level
    => Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Maybe Int
    -> m ()
showRule configNode = do
    ReplState { axioms, graph = Strategy.ExecutionGraph { graph } } <- get
    node <- Lens.use lensNode
    let node' = maybe node id configNode
    if node' `elem` Graph.nodes graph
        then do
            putStrLn' $ "Rule for node " <> show node' <> " is:"
            unparseNodeLabels
                . Graph.inn'
                . Graph.context graph
                $ node'
            let mrule = getRewriteRuleFromLabel
                            . Graph.inn'
                            . Graph.context graph
                            $ node'
            case mrule of
                Just rule -> do
                    let mid = getRuleIndex
                                . Attribute.identifier
                                . Rule.attributes
                                . Rule.getRewriteRule
                                $ rule
                    putStrLn' $ maybe
                        "Error: identifier attribute wasn't initialized."
                        (axiomOrClaim (length axioms))
                        mid
                Nothing ->
                    putStrLn' "No rule was applied."
        else putStrLn' "Invalid node!"

axiomOrClaim :: Int -> Int -> String
axiomOrClaim len iden
  | iden < len = "Axiom " <> show iden
  | otherwise  = "Claim " <> show (iden - len)

showPrecBranch
    :: Claim claim
    => Maybe Int
    -> ReplM claim level ()
showPrecBranch mnode = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    node <- Lens.use lensNode
    let node' = maybe node id mnode
    if node' `elem` Graph.nodes graph
       then putStrLn' . show $ loop (loopCond graph) node'
       else putStrLn' "Invalid node!"
  where
    loopCond gph n
      | (Graph.outdeg gph n) <= 1 && (not . null . Graph.pre gph $ n)
          = Left $ head (Graph.pre gph n)
      | otherwise = Right n

showChildren
    :: Claim claim
    => Maybe Int
    -> ReplM claim level ()
showChildren mnode = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    node <- Lens.use lensNode
    let node' = maybe node id mnode
    if node' `elem` Graph.nodes graph
       then putStrLn' $ show (Graph.suc graph node')
       else putStrLn' "Invalid node!"

redirect
    :: forall level claim
    .  MetaOrObject level
    => Claim claim
    => ReplCommand
    -> FilePath
    -> ReplM claim level ()
redirect cmd path = do
    st <- get
    _ <- lift $ evalStateT (replInterpreter redirectToFile cmd) st
    putStrLn' "File created."
    pure ()
  where
    redirectToFile :: String -> IO ()
    redirectToFile = writeFile path

tryAxiomClaim
    :: forall level claim
    .  MetaOrObject level
    => Claim claim
    => level ~ Object
    => Either AxiomIndex ClaimIndex
    -> ReplM claim level ()
tryAxiomClaim eac = do
    ReplState { axioms, claims, claim, graph, node, stepper } <- get
    case getAxiomOrClaim axioms claims node of
        Nothing ->
            putStrLn' "Could not find axiom or claim,\
                 \or attempt to use claim as first step"
        Just eac' -> do
            if Graph.outdeg (Strategy.graph graph) node == 0
                then do
                    graph'@Strategy.ExecutionGraph { graph = gr } <-
                        lift $ stepper
                            claim
                            (either (const []) id eac')
                            (either id (const []) eac')
                            graph
                            node
{-
    After trying to apply an axiom/claim, there are three possible cases:
    - If there are no resulting nodes then the rule
    couldn't be applied.
    - If there is a single resulting node then the rule
    was applied successfully.
    - If there are more than one resulting nodes then
    the rule was applied successfully but it wasn't sufficient.
    If a remainder exists after applying a set of axioms
    the current unification algorithm considers this
    remainder to be Stuck. In this case, though, since only one
    rule of the set is applied we must consider the
    possibility that another axiom may be further applied
    successfully on the resulting remainder, so as a workaround
    we will change the state of these nodes from Stuck to
    RewritePattern to allow further applications.
    If indeed no other axiom can be applied on the remainder,
    then a single step command will identify it as being Stuck.
-}
                    case Graph.suc' $ Graph.context gr node of
                        [] -> showUnificationFailure eac' node
                        [node'] -> do
                            lensGraph .= graph'
                            lensNode .= node'
                            putStrLn' "Unification successful."
                        xs -> do
                            lensGraph .=
                                Strategy.ExecutionGraph
                                    (Strategy.root graph')
                                    (tryAgainOnNodes xs gr)
                            putStrLn' "Unification successful."
                else putStrLn' "Node is already evaluated"
  where
    tryAgainOnNodes ns gph =
        Graph.gmap (stuckToRewrite ns) gph

    stuckToRewrite xs ct@(to, n, lab, from)
        | n `elem` xs =
            case lab of
                Stuck patt -> (to, n, RewritePattern patt, from)
                _ -> ct
        | otherwise = ct
    getAxiomOrClaim
        :: [Axiom level]
        -> [claim]
        -> Graph.Node
        -> Maybe (Either [Axiom level] [claim])
    getAxiomOrClaim axioms claims node =
        bimap pure pure <$> resolve axioms claims node
    resolve
        :: [Axiom level]
        -> [claim]
        -> Graph.Node
        -> Maybe (Either (Axiom level) (claim))
    resolve axioms claims node =
        case eac of
            Left  (AxiomIndex aid) -> Left  <$> axioms `atZ` aid
            Right (ClaimIndex cid)
              | node == 0 -> Nothing
              | otherwise -> Right <$> claims `atZ` cid
    showUnificationFailure
        :: Either [Axiom level] [claim]
        -> Graph.Node
        -> ReplM claim level ()
    showUnificationFailure axiomOrClaim' node = do
        case extractLeftPattern axiomOrClaim' of
            Nothing    -> putStrLn' "No axiom or claim found."
            Just first -> do
                second <- getCurrentConfig node
                strategyPattern
                    StrategyPatternTransformer
                        { bottomValue        = putStrLn' "Cannot unify bottom"
                        , rewriteTransformer = unify first . term
                        , stuckTransformer   = unify first . term
                        }
                    second
    unify
        :: StepPattern Object Variable
        -> StepPattern Object Variable
        -> ReplM claim level ()
    unify first second = do
        unifier <- Lens.use lensUnifier
        mdoc <-
            Monad.Trans.lift . runUnifierWithExplanation $ unifier first second
        case mdoc of
            Nothing -> putStrLn' "No unification error found."
            Just doc -> putStrLn' $ show doc
    extractLeftPattern
        :: Either [Axiom level] [claim]
        -> Maybe (StepPattern level Variable)
    extractLeftPattern =
        listToMaybe
            . fmap (left . getRewriteRule)
            . either (fmap unAxiom) (fmap coerce)
    getCurrentConfig node = do
        Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
        return . Graph.lab' . Graph.context graph $ node


label
    :: forall level m claim
    .  Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Maybe String
    -> m ()
label =
    \case
        Nothing -> showLabels
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
        res <> "\n  " <> key <> ": " <> (show node)

labelAdd
    :: forall level m claim
    .  Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => String
    -> Maybe Int
    -> m ()
labelAdd lbl mn = do
    Strategy.ExecutionGraph { graph } <- Lens.use lensGraph
    node <- Lens.use lensNode
    let node' = maybe node id mn
    labels <- Lens.use lensLabels
    if lbl `Map.notMember` labels && node' `elem` Graph.nodes graph
       then do
           lensLabels .= Map.insert lbl node' labels
           putStrLn' "Label added."
       else putStrLn' "Label already exists or the node isn't in the graph."

labelDel
    :: forall level m claim
    .  MonadState (ReplState claim level) m
    => Claim claim
    => MonadWriter String m
    => String
    -> m ()
labelDel lbl = do
    labels <- Lens.use lensLabels
    if lbl `Map.member` labels
       then do
           lensLabels .= Map.delete lbl labels
           putStrLn' "Removed label."
       else putStrLn' "Label doesn't exist."

clear
    :: forall level m claim
    .  Claim claim
    => MonadState (ReplState claim level) m
    => MonadWriter String m
    => Maybe Int
    -> m ()
clear =
    \case
        Nothing -> Just <$> Lens.use lensNode >>= clear
        Just node
          | node == 0 -> putStrLn' "Cannot clear initial node (0)."
          | otherwise -> go node
  where
    go :: Int -> m ()
    go node = do
        eg@Strategy.ExecutionGraph { graph = gr } <- Lens.use lensGraph
        let
            nodes = collect (next gr) node
            gr' = Graph.delNodes nodes gr
            prevNode =
                maybe 0 id
                    . listToMaybe
                    . fmap fst
                    $ Graph.lpre gr node
        lensGraph .= eg { Strategy.graph = gr' }
        lensNode .= prevNode
        putStrLn' $ "Removed " <> show (length nodes) <> " node(s)."

    next :: InnerGraph -> Graph.Node -> [Graph.Node]
    next gr n = fst <$> Graph.lsuc gr n

    collect :: (a -> [a]) -> a -> [a]
    collect f x = x : [ z | y <- f x, z <- collect f y]

saveSession
    :: forall level m claim
    .  MonadState (ReplState level claim) m
    => MonadWriter String m
    => MonadIO m
    => FilePath
    -> m ()
saveSession path = do
   content <- seqUnlines <$> Lens.use lensCommands
   liftIO $ writeFile path content
   putStrLn' "Done."
 where
   seqUnlines :: Seq String -> String
   seqUnlines = unlines . toList

printRewriteRule :: MonadWriter String m => RewriteRule level Variable -> m ()
printRewriteRule rule = do
    putStrLn' $ unparseToString rule
    putStrLn'
        . show
        . Pretty.pretty
        . extractSourceAndLocation
        $ rule

performSingleStep
    :: Claim claim => ReplM claim level StepResult
performSingleStep = do
    ReplState { claims , axioms , graph , claim , node, stepper } <- get
    graph'@Strategy.ExecutionGraph { graph = gr }  <-
        lift $ stepper claim claims axioms graph node
    lensGraph .= graph'
    let context = Graph.context gr node
    case Graph.suc' context of
      [] -> pure NoChildNodes
      [configNo] -> do
          lensNode .= configNo
          pure Success
      neighbors -> pure (Branch neighbors)

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

-- | Performs n proof steps, picking the next node unless branching occurs.
-- Returns 'Left' while it has to continue looping, and 'Right' when done
-- or when execution branches or proof finishes earlier than the counter.
--
-- See 'loopM' for details.
performStepNoBranching
    :: Claim claim
    => (Int, StepResult)
    -- ^ (current step, last result)
    -> ReplM claim level (Either (Int, StepResult) (Int, StepResult))
performStepNoBranching (0, res) =
    pure $ Right (0, res)
performStepNoBranching (n, Success) = do
    res <- performSingleStep
    pure $ Left (n-1, res)
performStepNoBranching (n, res) =
    pure $ Right (n, res)

unparseStrategy
    :: forall level
    .  MetaOrObject level
    => [String]
    -> CommonStrategyPattern level
    -> String
unparseStrategy omitList =
    strategyPattern StrategyPatternTransformer
        { rewriteTransformer = \pat -> unparseToString (hide <$> pat)
        , stuckTransformer =
            \pat -> "Stuck: \n" <> unparseToString (hide <$> pat)
        , bottomValue = "Reached bottom"
        }
  where
    hide :: StepPattern level Variable -> StepPattern level Variable
    hide =
        Recursive.unfold $ \stepPattern ->
            case Recursive.project stepPattern of
                ann :< ApplicationPattern app
                  | shouldBeExcluded (applicationSymbolOrAlias app) ->
                    -- Do not display children
                    ann :< ApplicationPattern (withoutChildren app)
                projected -> projected
      where
        withoutChildren app = app { applicationChildren = [] }

    shouldBeExcluded =
       (flip elem) omitList
           . Text.unpack
           . Identifier.getId
           . symbolOrAliasConstructor

unparseNodeLabels
    :: MonadWriter String m
    => [ (Graph.Node, Graph.Node, Seq (RewriteRule Object Variable)) ]
    -> m ()
unparseNodeLabels =
    traverse_ printRewriteRule
    . join
    . fmap (toList . third)
  where
    third :: (a, b, c) -> c
    third (_, _, c) = c

getRewriteRuleFromLabel
    :: [ (Graph.Node, Graph.Node, Seq (RewriteRule Object Variable)) ]
    -> Maybe (RewriteRule Object Variable)
getRewriteRuleFromLabel =
    listToMaybe
    . join
    . fmap (toList . third)
  where
      third :: (a, b, c) -> c
      third (_, _, c) = c

extractSourceAndLocation
    :: RewriteRule level Variable
    -> SourceLocation
extractSourceAndLocation
    (RewriteRule (RulePattern{ Axiom.attributes })) =
        Attribute.sourceLocation attributes

printNotFound :: MonadWriter String m => m ()
printNotFound = putStrLn' "Variable or index not found"

putStrLn' :: MonadWriter String m => String -> m ()
putStrLn' str = tell $ str <> "\n"

showDotGraph :: Int -> InnerGraph-> IO ()
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
            Just rule -> maybe "Unknown " Text.Lazy.pack
                      . fmap (axiomOrClaim len)
                      . getRuleIndex
                      . Attribute.identifier
                      . Rule.attributes
                      . Rule.getRewriteRule
                      $ rule

data StepResult
    = NoChildNodes
    | Branch [Graph.Node]
    | Success
    deriving Show

emptyExecutionGraph :: Claim claim => claim -> ExecutionGraph
emptyExecutionGraph =
    Strategy.emptyExecutionGraph . extractConfig . RewriteRule . coerce

extractConfig
    :: RewriteRule level Variable
    -> CommonStrategyPattern level
extractConfig (RewriteRule RulePattern { left, requires }) =
    RewritePattern $ Predicated left requires mempty
