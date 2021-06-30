{- |
Module      : Kore.Repl.Data
Description : REPL data structures.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}
module Kore.Repl.Data (
    ReplCommand (..),
    helpText,
    ExecutionGraph,
    AxiomIndex (..),
    ClaimIndex (..),
    RuleName (..),
    RuleReference (..),
    ReplNode (..),
    Axiom,
    AppliedRule,
    ReplState (..),
    ReplOutput (..),
    ReplOut (..),
    PrintAuxOutput (..),
    PrintKoreOutput (..),
    Config (..),
    NodeState (..),
    GraphProofStatus (..),
    AliasDefinition (..),
    ReplAlias (..),
    AliasArgument (..),
    AliasError (..),
    InnerGraph,
    shouldStore,
    commandSet,
    runUnifierWithoutExplanation,
    StepResult (..),
    LogType (..),
    ReplScript (..),
    ReplMode (..),
    ScriptModeOutput (..),
    OutputFile (..),
    makeAuxReplOutput,
    makeKoreReplOutput,
    GraphView (..),
    GeneralLogOptions (..),
    generalLogOptionsTransformer,
    debugAttemptEquationTransformer,
    debugApplyEquationTransformer,
    debugEquationTransformer,
    entriesForHelp,
    TryApplyRuleResult (..),
) where

import Control.Concurrent.MVar
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.PatriciaTree (
    Gr,
 )
import qualified Data.GraphViz as Graph
import Data.List (
    sort,
 )
import Data.Map.Strict (
    Map,
 )
import Data.Sequence (
    Seq,
 )
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import qualified GHC.Generics as GHC
import Kore.Attribute.Definition
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike (
    TermLike,
 )
import Kore.Log (
    ActualEntry (..),
    LogAction (..),
 )
import qualified Kore.Log as Log
import qualified Kore.Log.Registry as Log
import Kore.Reachability hiding (
    AppliedRule,
 )
import qualified Kore.Reachability as Reachability
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Rewrite.Strategy as Strategy
import Kore.Simplify.Data (
    MonadSimplify (..),
 )
import qualified Kore.Simplify.Not as Not
import Kore.Syntax.Module (
    ModuleName (..),
 )
import Kore.Unification.UnifierT (
    UnifierT (..),
 )
import qualified Kore.Unification.UnifierT as Monad.Unify
import Logic
import Numeric.Natural
import Prelude.Kore

{- | Represents an optional file name which contains a sequence of
 repl commands.
-}
newtype ReplScript = ReplScript
    { unReplScript :: Maybe FilePath
    }
    deriving stock (Eq, Show)

data ReplMode = Interactive | RunScript
    deriving stock (Eq, Show)

data ScriptModeOutput = EnableOutput | DisableOutput
    deriving stock (Eq, Show)

newtype OutputFile = OutputFile
    { unOutputFile :: Maybe FilePath
    }
    deriving stock (Eq, Show)

newtype AxiomIndex = AxiomIndex
    { unAxiomIndex :: Int
    }
    deriving stock (Eq, Show)

newtype ClaimIndex = ClaimIndex
    { unClaimIndex :: Int
    }
    deriving stock (Eq, Ord, Show)

newtype ReplNode = ReplNode
    { unReplNode :: Graph.Node
    }
    deriving stock (Eq, Show)

newtype RuleName = RuleName
    { unRuleName :: String
    }
    deriving stock (Eq, Show)

{- | The repl keeps Kore output separated from any other kinds of auxiliary output.
 This makes it possible to treat the output differently by using different
 printing functions. For example, the pipe command will only send KoreOut to the
 process' input handle.
-}
newtype ReplOutput = ReplOutput {unReplOutput :: [ReplOut]}
    deriving stock (Eq, Show)
    deriving newtype (Semigroup, Monoid)

-- | Newtypes for printing functions called by Kore.Repl.Interpreter.replInterpreter0
newtype PrintAuxOutput = PrintAuxOutput
    {unPrintAuxOutput :: String -> IO ()}

newtype PrintKoreOutput = PrintKoreOutput
    {unPrintKoreOutput :: String -> IO ()}

data ReplOut = AuxOut String | KoreOut String
    deriving stock (Eq, Show)

data AliasDefinition = AliasDefinition
    { name :: String
    , arguments :: [String]
    , command :: String
    }
    deriving stock (Eq, Show)

data AliasArgument
    = SimpleArgument String
    | QuotedArgument String
    deriving stock (Eq, Show)

data ReplAlias = ReplAlias
    { name :: String
    , arguments :: [AliasArgument]
    }
    deriving stock (Eq, Show)

data LogType
    = NoLogging
    | LogToStdErr
    | LogToFile !FilePath
    deriving stock (Eq, Show)

data RuleReference
    = ByIndex (Either AxiomIndex ClaimIndex)
    | ByName RuleName
    deriving stock (Eq, Show)

{- | Option for viewing the full (expanded) graph
 or the collapsed graph where only the branching nodes,
 their direct descendents and leafs are visible
-}
data GraphView
    = Collapsed
    | Expanded
    deriving stock (Eq, Show)

-- | Log options which can be changed by the log command.
data GeneralLogOptions = GeneralLogOptions
    { logType :: !Log.KoreLogType
    , logLevel :: !Log.Severity
    , timestampsSwitch :: !Log.TimestampsSwitch
    , logEntries :: !Log.EntryTypes
    }
    deriving stock (Eq, Show)

generalLogOptionsTransformer ::
    GeneralLogOptions ->
    Log.KoreLogOptions ->
    Log.KoreLogOptions
generalLogOptionsTransformer
    logOptions@(GeneralLogOptions _ _ _ _)
    koreLogOptions =
        koreLogOptions
            { Log.logLevel = logLevel
            , Log.logEntries = logEntries
            , Log.logType = logType
            , Log.timestampsSwitch = timestampsSwitch
            }
      where
        GeneralLogOptions
            { logLevel
            , logType
            , logEntries
            , timestampsSwitch
            } = logOptions

debugAttemptEquationTransformer ::
    Log.DebugAttemptEquationOptions ->
    Log.KoreLogOptions ->
    Log.KoreLogOptions
debugAttemptEquationTransformer
    debugAttemptEquationOptions
    koreLogOptions =
        koreLogOptions
            { Log.debugAttemptEquationOptions = debugAttemptEquationOptions
            }

debugApplyEquationTransformer ::
    Log.DebugApplyEquationOptions ->
    Log.KoreLogOptions ->
    Log.KoreLogOptions
debugApplyEquationTransformer
    debugApplyEquationOptions
    koreLogOptions =
        koreLogOptions
            { Log.debugApplyEquationOptions = debugApplyEquationOptions
            }

debugEquationTransformer ::
    Log.DebugEquationOptions ->
    Log.KoreLogOptions ->
    Log.KoreLogOptions
debugEquationTransformer
    debugEquationOptions
    koreLogOptions =
        koreLogOptions
            { Log.debugEquationOptions = debugEquationOptions
            }

{- | List of available commands for the Repl. Note that we are always in a proof
 state. We pick the first available Claim when we initialize the state.
-}
data ReplCommand
    = -- | This is the default action in case parsing all others fail.
      ShowUsage
    | -- | Shows the help message.
      Help
    | -- | Show the nth claim or the current claim.
      ShowClaim !(Maybe (Either ClaimIndex RuleName))
    | -- | Show the nth axiom.
      ShowAxiom !(Either AxiomIndex RuleName)
    | -- | Drop the current proof state and re-initialize for the nth claim.
      Prove !(Either ClaimIndex RuleName)
    | -- | Show the current execution graph.
      ShowGraph
        !(Maybe GraphView)
        !(Maybe FilePath)
        !(Maybe Graph.GraphvizOutput)
    | -- | Do n proof steps from current node.
      ProveSteps !Natural
    | -- | Do n proof steps (through branchings) from the current node.
      ProveStepsF !Natural
    | -- | Select a different node in the graph.
      SelectNode !ReplNode
    | -- | Show the configuration from the current node.
      ShowConfig !(Maybe ReplNode)
    | -- | Show the destination from the current node.
      ShowDest !(Maybe ReplNode)
    | -- | Adds or removes cell to omit list, or shows current omit list.
      OmitCell !(Maybe String)
    | -- | Show leafs which can continue evaluation and leafs which are stuck
      ShowLeafs
    | -- | Show the rule(s) that got us to this configuration.
      ShowRule !(Maybe ReplNode)
    | -- | Show the rules which were applied from the first node
      -- to reach the second.
      ShowRules !(ReplNode, ReplNode)
    | -- | Show the first preceding branch.
      ShowPrecBranch !(Maybe ReplNode)
    | -- | Show direct children of node.
      ShowChildren !(Maybe ReplNode)
    | -- | Show all node labels or jump to a label.
      Label !(Maybe String)
    | -- | Add a label to a node.
      LabelAdd !String !(Maybe ReplNode)
    | -- | Remove a label.
      LabelDel !String
    | -- | Prints the output of the inner command to the file.
      Redirect ReplCommand FilePath
    | -- | Attempt to apply axiom or claim to current node.
      Try !RuleReference
    | -- | Force application of an axiom or claim to current node.
      TryF !RuleReference
    | -- | Remove child nodes from graph.
      Clear !(Maybe ReplNode)
    | -- | Pipes a repl command into an external script.
      Pipe ReplCommand !String ![String]
    | -- | Writes all commands executed in this session to a file on disk.
      SaveSession FilePath
    | -- | Saves a partial proof to a file on disk.
      SavePartialProof (Maybe Natural) FilePath
    | -- | Appends the output of a command to a file.
      AppendTo ReplCommand FilePath
    | -- | Alias a command.
      Alias AliasDefinition
    | -- | Try running an alias.
      TryAlias ReplAlias
    | -- | Load script from file
      LoadScript FilePath
    | -- | Show proof status of each claim
      -- TODO(Ana): 'Log (KoreLogOptions -> KoreLogOptions)', this would need
      -- the parts of the code which depend on the 'Show' instance of 'ReplCommand'
      -- to change. Do the same for Debug..Equation.
      ProofStatus
    | -- | Setup the Kore logger.
      Log GeneralLogOptions
    | -- | Log debugging information about attempting to
      -- apply specific equations.
      DebugAttemptEquation Log.DebugAttemptEquationOptions
    | -- | Log when specific equations apply.
      DebugApplyEquation Log.DebugApplyEquationOptions
    | -- | Log the attempts and the applications of specific
      -- equations.
      DebugEquation Log.DebugEquationOptions
    | -- | Exit the repl.
      Exit
    deriving stock (Eq, Show)

commandSet :: Set String
commandSet =
    Set.fromList
        [ "help"
        , "claim"
        , "axiom"
        , "prove"
        , "graph"
        , "step"
        , "stepf"
        , "select"
        , "config"
        , "omit"
        , "leafs"
        , "rule"
        , "prec-branch"
        , "proof-status"
        , "children"
        , "label"
        , "try"
        , "tryf"
        , "clear"
        , "save-session"
        , "alias"
        , "load"
        , "log"
        , "exit"
        ]

-- | Please remember to update this text whenever you update the ADT above.
helpText :: String
helpText =
    "Available commands in the Kore REPL: \n\
    \help                                     shows this help message\n\
    \claim [n|<name>]                         shows the nth claim, the claim with\
    \ <name> or (default) the currently\
    \ focused claim\n\
    \axiom <n|name>                           shows the nth axiom or the axiom\
    \ with <name>\n\
    \prove <n|name>                           initializes proof mode for the nth\
    \ claim or for the claim with <name>\n\
    \graph [view] [file] [format]             shows the current proof graph (*),\
    \ 'expanded' or 'collapsed';\
    \ or saves it as jpeg, png, pdf or svg\n\
    \step [n]                                 attempts to run 'n' proof steps at\
    \ the current node (n=1 by default)\n\
    \stepf [n]                                like step, but goes through\
    \ branchings to the first\
    \ interesting branching node (**)\n\
    \select <n>                               select node id 'n' from the graph\n\
    \config [n]                               shows the config for node 'n'\
    \ (defaults to current node)\n\
    \dest [n]                                 shows the destination for node 'n'\
    \ (defaults to current node)\n\
    \omit [cell]                              adds or removes cell to omit list\
    \ (defaults to showing the omit\
    \ list)\n\
    \leafs                                    shows unevaluated or stuck leafs\n\
    \rule [n]                                 shows the rule for node 'n'\
    \ (defaults to current node)\n\
    \rules <n1> <n2>                          shows the rules applied on the path\
    \ between nodes n1 and n2\n\
    \prec-branch [n]                          shows first preceding branch\
    \ (defaults to current node)\n\
    \children [n]                             shows direct children of node\
    \ (defaults to current node)\n\
    \label                                    shows all node labels\n\
    \label <l>                                jump to a label\n\
    \label <+l> [n]                           add a new label for a node\
    \ (defaults to current node)\n\
    \label <-l>                               remove a label\n\
    \try (<a|c><num>)|<name>                  attempts <a>xiom or <c>laim at\
    \ index <num> or rule with <name>\n\
    \tryf (<a|c><num>)|<name>                 like try, but if successful, it will apply the axiom or claim.\n\
    \clear [n]                                removes all the node's children from the\
    \ proof graph (***)\
    \ (defaults to current node)\n\
    \save-session file                        saves the current session to file\n\
    \save-partial-proof [n] file              writes a new claim with the\
    \ config 'n' as its LHS and all\
    \ other claims marked as trusted\n\
    \alias <name> = <command>                 adds as an alias for <command>\n\
    \<alias>                                  runs an existing alias\n\
    \load file                                loads the file as a repl script\n\
    \proof-status                             shows status for each claim\n\
    \log [<severity>] \"[\"<entry>\"]\"           configures logging; <severity> can be debug ... error; [<entry>] is a list formed by types below;\n\
    \    <type> <switch-timestamp>            <type> can be stderr or 'file filename'; <switch-timestamp> can be (enable|disable)-log-timestamps;\n\
    \debug[-type-]equation [eqId1] [eqId2] .. show debugging information for specific equations;\
    \ [-type-] can be '-attempt-', '-apply-' or '-',\n\
    \exit                                     exits the repl\
    \\n\n\
    \Available modifiers:\n\
    \<command> > file                         prints the output of 'command'\
    \ to file\n\
    \<command> >> file                        appends the output of 'command'\
    \ to file\n\
    \<command> | external_script              pipes command to external script\
    \ and prints the result in the\
    \ repl; can be redirected using > or >>\n\
    \\n\
    \Rule names can be added in two ways:\n\
    \    a) rule <k> ... </k> [label(myName)]\n\
    \       - can be used as-is\n\
    \       - ! do not add names which match the indexing syntax for the try command\n\
    \    b) rule [myName] : <k> ... </k>\n\
    \       - need to be prefixed with the module name, e.g. IMP.myName\n\
    \\nAvailable entry types:\n"
        <> entriesForHelp
        <> "\n\
           \(*) If an edge is labeled CheckImplication it means that during that step\n\
           \ the prover detected that the claim was either proven or that it could not be\
           \ rewritten any further (stuck).\n\
           \    When the application of a rewrite rule results in a remainder and no other\
           \ rewrite rules apply, then the edge pointing to the remaining state is labeled Remaining.\n\
           \    A green node represents the proof has completed on\
           \ that respective branch. \n\
           \    A red node represents a stuck configuration.\n\
           \(**) An interesting branching node has at least two children which\n\
           \ contain non-bottom leaves in their subtrees. If no such node exists,\n\
           \ the current node is advanced to the (only) non-bottom leaf. If no such\n\
           \ leaf exists (i.e the proof is complete), the current node remains the same\n\
           \ and a message is emitted.\n\
           \(***) The clear command doesn't allow the removal of nodes which are direct\n\
           \ descendants of branchings. The steps which create branchings cannot be\n\
           \ partially redone. Therefore, if this were allowed it would result in invalid proofs.\n"
        <> "\nFor more details see https://github.com/kframework/kore/wiki/Kore-REPL#available-commands-in-the-kore-repl\n"

entriesForHelp :: String
entriesForHelp =
    zipWith3
        (\e1 e2 e3 -> align e1 <> align e2 <> align e3)
        column1
        column2
        column3
        & unlines
  where
    entries :: [String]
    entries =
        Log.entryTypeReps
            & fmap show
            & sort
            & (<> ["", ""])
    align entry = entry <> replicate (40 - length entry) ' '
    columnLength = length entries `div` 3
    (column1And2, column3) = splitAt (2 * columnLength) entries
    (column1, column2) = splitAt columnLength column1And2

{- | Determines whether the command needs to be stored or not. Commands that
 affect the outcome of the proof are stored.
-}
shouldStore :: ReplCommand -> Bool
shouldStore =
    \case
        ShowUsage -> False
        Help -> False
        ShowClaim _ -> False
        ShowAxiom _ -> False
        ShowGraph _ _ _ -> False
        ShowConfig _ -> False
        ShowLeafs -> False
        ShowRule _ -> False
        ShowPrecBranch _ -> False
        ShowChildren _ -> False
        SaveSession _ -> False
        ProofStatus -> False
        Try _ -> False
        Exit -> False
        _ -> True

-- Type synonym for the actual type of the execution graph.
type ExecutionGraph = Strategy.ExecutionGraph CommonClaimState AppliedRule

type InnerGraph = Gr CommonClaimState (Seq AppliedRule)

type Axiom = Rule SomeClaim
type AppliedRule = Reachability.AppliedRule SomeClaim

-- | State for the repl.
data ReplState = ReplState
    { -- | List of available axioms
      axioms :: [Axiom]
    , -- | List of claims to be proven
      claims :: [SomeClaim]
    , -- | Currently focused claim in the repl
      claim :: SomeClaim
    , -- | Index of the currently focused claim in the repl
      claimIndex :: ClaimIndex
    , -- | Execution graph for the current proof; initialized with root = claim
      graphs :: Map ClaimIndex ExecutionGraph
    , -- | Currently selected node in the graph; initialized with node = root
      node :: ReplNode
    , -- | All commands evaluated by the current repl session
      commands :: Seq String
    , -- | The omit list, initially empty
      omit :: Set String
    , -- | Map from labels to nodes
      labels :: Map ClaimIndex (Map String ReplNode)
    , -- | Map of command aliases
      aliases :: Map String AliasDefinition
    , -- | The log level, log scopes and log type decide what gets logged and
      -- where.
      koreLogOptions :: !Log.KoreLogOptions
    }
    deriving stock (GHC.Generic)

-- | Configuration environment for the repl.
data Config m = Config
    { -- | Stepper function
      stepper ::
        [SomeClaim] ->
        [Axiom] ->
        ExecutionGraph ->
        ReplNode ->
        m ExecutionGraph
    , -- | Unifier function, it is a partially applied 'unificationProcedure'
      --   where we discard the result since we are looking for unification
      --   failures
      unifier ::
        SideCondition RewritingVariableName ->
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        UnifierT m (Condition RewritingVariableName)
    , -- | Logger function, see 'logging'.
      logger :: MVar (LogAction IO ActualEntry)
    , -- | Output resulting pattern to this file.
      outputFile :: OutputFile
    , mainModuleName :: ModuleName
    , kFileLocations :: KFileLocations
    }
    deriving stock (GHC.Generic)

-- | Result after running one or multiple proof steps.
data StepResult
    = -- | reached end of proof on current branch
      NoResult
    | -- | single follow-up configuration
      SingleResult ReplNode
    | -- | configuration branched
      BranchResult [ReplNode]
    deriving stock (Show)

data NodeState = StuckNode | UnevaluatedNode
    deriving stock (Eq, Ord, Show)

data AliasError
    = NameAlreadyDefined
    | UnknownCommand

data GraphProofStatus
    = NotStarted
    | Completed
    | InProgress [Graph.Node]
    | StuckProof [Graph.Node]
    | TrustedClaim
    deriving stock (Eq, Show)

makeAuxReplOutput :: String -> ReplOutput
makeAuxReplOutput str =
    ReplOutput . return . AuxOut $ str <> "\n"

makeKoreReplOutput :: String -> ReplOutput
makeKoreReplOutput str =
    ReplOutput . return . KoreOut $ str <> "\n"

runUnifierWithoutExplanation ::
    forall m a.
    MonadSimplify m =>
    UnifierT m a ->
    m (Maybe (NonEmpty a))
runUnifierWithoutExplanation unifier =
    failEmptyList <$> unificationResults
  where
    unificationResults :: m [a]
    unificationResults = Monad.Unify.runUnifierT Not.notSimplifier unifier
    failEmptyList :: [a] -> Maybe (NonEmpty a)
    failEmptyList results =
        case results of
            [] -> Nothing
            r : rs -> Just (r :| rs)

data TryApplyRuleResult
    = DoesNotApply
    | GetsProven
    | OneResult ReplNode
    | MultipleResults
    deriving stock (Show, Eq)
