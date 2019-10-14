{-|
Module      : Kore.Repl.Data
Description : REPL data structures.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl.Data
    ( ReplCommand (..)
    , helpText
    , ExecutionGraph
    , AxiomIndex (..), ClaimIndex (..)
    , RuleName (..), RuleReference(..)
    , ReplNode (..)
    , ReplState (..)
    , ReplOutput (..)
    , ReplOut (..)
    , PrintAuxOutput (..)
    , PrintKoreOutput (..)
    , Config (..)
    , NodeState (..)
    , GraphProofStatus (..)
    , AliasDefinition (..), ReplAlias (..), AliasArgument(..), AliasError (..)
    , InnerGraph
    , shouldStore
    , commandSet
    , UnifierWithExplanation (..)
    , runUnifierWithExplanation
    , StepResult(..)
    , LogType (..)
    , LogScope (..)
    , ReplScript (..)
    , ReplMode (..)
    , OutputFile (..)
    , makeAuxReplOutput, makeKoreReplOutput
    , makeLogScope
    ) where

import Control.Applicative
    ( Alternative
    )
import Control.Concurrent.MVar
import Control.Monad.Trans.Accum
    ( AccumT
    , runAccumT
    )
import qualified Control.Monad.Trans.Accum as Monad.Accum
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Graph.Inductive.PatriciaTree
    ( Gr
    )
import Data.List.NonEmpty
    ( NonEmpty (..)
    )
import Data.Map.Strict
    ( Map
    )
import Data.Maybe
    ( fromMaybe
    )
import Data.Monoid
    ( First (..)
    )
import Data.Sequence
    ( Seq
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Generics as GHC
import Numeric.Natural

import qualified Kore.Internal.Predicate as IPredicate
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Logger.Output as Logger
import Kore.Profiler.Data
    ( MonadProfiler
    )
import Kore.Step.Simplification.Data
    ( MonadSimplify
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Strategies.Goal
import Kore.Strategies.Verification
    ( CommonProofState
    )
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.Unification.Error
import Kore.Unification.Unify
    ( MonadUnify
    , UnifierT (..)
    )
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser
    ( unparse
    )
import SMT
    ( MonadSMT
    )

-- | Represents an optional file name which contains a sequence of
-- repl commands.
newtype ReplScript = ReplScript
    { unReplScript :: Maybe FilePath
    } deriving (Eq, Show)

data ReplMode = Interactive | RunScript
    deriving (Eq, Show)

newtype OutputFile = OutputFile
    { unOutputFile :: Maybe FilePath
    } deriving (Eq, Show)

newtype AxiomIndex = AxiomIndex
    { unAxiomIndex :: Int
    } deriving (Eq, Show)

newtype ClaimIndex = ClaimIndex
    { unClaimIndex :: Int
    } deriving (Eq, Ord, Show)

newtype ReplNode = ReplNode
    { unReplNode :: Graph.Node
    } deriving (Eq, Show)

newtype RuleName = RuleName
    { unRuleName :: String
    } deriving (Eq, Show)

-- | The repl keeps Kore output separated from any other kinds of auxiliary output.
-- This makes it possible to treat the output differently by using different
-- printing functions. For example, the pipe command will only send KoreOut to the
-- process' input handle.
newtype ReplOutput =
    ReplOutput
    { unReplOutput :: [ReplOut]
    } deriving (Eq, Show, Semigroup, Monoid)

-- | Newtypes for printing functions called by Kore.Repl.Interpreter.replInterpreter0
newtype PrintAuxOutput = PrintAuxOutput
    { unPrintAuxOutput :: String -> IO () }

newtype PrintKoreOutput = PrintKoreOutput
    { unPrintKoreOutput :: String -> IO () }

data ReplOut = AuxOut String | KoreOut String
    deriving (Eq, Show)

data AliasDefinition = AliasDefinition
    { name      :: String
    , arguments :: [String]
    , command   :: String
    } deriving (Eq, Show)

data AliasArgument
  = SimpleArgument String
  | QuotedArgument String
  deriving (Eq, Show)

data ReplAlias = ReplAlias
    { name      :: String
    , arguments :: [AliasArgument]
    } deriving (Eq, Show)

data LogType
    = NoLogging
    | LogToStdOut
    | LogToFile !FilePath
    deriving (Eq, Show)

newtype LogScope =
    LogScope
    { unLogScope :: Set.Set Logger.Scope }
    deriving (Eq, Show, Semigroup, Monoid)

makeLogScope :: [String] -> LogScope
makeLogScope scopes =
    LogScope
    . Set.fromList
    $ fmap (Logger.Scope . Text.pack) scopes

data RuleReference
    = ByIndex (Either AxiomIndex ClaimIndex)
    | ByName RuleName
    deriving (Eq, Show)

-- | List of available commands for the Repl. Note that we are always in a proof
-- state. We pick the first available Claim when we initialize the state.
data ReplCommand
    = ShowUsage
    -- ^ This is the default action in case parsing all others fail.
    | Help
    -- ^ Shows the help message.
    | ShowClaim !(Maybe (Either ClaimIndex RuleName))
    -- ^ Show the nth claim or the current claim.
    | ShowAxiom !(Either AxiomIndex RuleName)
    -- ^ Show the nth axiom.
    | Prove !(Either ClaimIndex RuleName)
    -- ^ Drop the current proof state and re-initialize for the nth claim.
    | ShowGraph !(Maybe FilePath)
    -- ^ Show the current execution graph.
    | ProveSteps !Natural
    -- ^ Do n proof steps from current node.
    | ProveStepsF !Natural
    -- ^ Do n proof steps (through branchings) from the current node.
    | SelectNode !ReplNode
    -- ^ Select a different node in the graph.
    | ShowConfig !(Maybe ReplNode)
    -- ^ Show the configuration from the current node.
    | OmitCell !(Maybe String)
    -- ^ Adds or removes cell to omit list, or shows current omit list.
    | ShowLeafs
    -- ^ Show leafs which can continue evaluation and leafs which are stuck
    | ShowRule !(Maybe ReplNode)
    -- ^ Show the rule(s) that got us to this configuration.
    | ShowPrecBranch !(Maybe ReplNode)
    -- ^ Show the first preceding branch.
    | ShowChildren !(Maybe ReplNode)
    -- ^ Show direct children of node.
    | Label !(Maybe String)
    -- ^ Show all node labels or jump to a label.
    | LabelAdd !String !(Maybe ReplNode)
    -- ^ Add a label to a node.
    | LabelDel !String
    -- ^ Remove a label.
    | Redirect ReplCommand FilePath
    -- ^ Prints the output of the inner command to the file.
    | Try !RuleReference
    -- ^ Attempt to apply axiom or claim to current node.
    | TryF !RuleReference
    -- ^ Force application of an axiom or claim to current node.
    | Clear !(Maybe ReplNode)
    -- ^ Remove child nodes from graph.
    | Pipe ReplCommand !String ![String]
    -- ^ Pipes a repl command into an external script.
    | SaveSession FilePath
    -- ^ Writes all commands executed in this session to a file on disk.
    | AppendTo ReplCommand FilePath
    -- ^ Appends the output of a command to a file.
    | Alias AliasDefinition
    -- ^ Alias a command.
    | TryAlias ReplAlias
    -- ^ Try running an alias.
    | LoadScript FilePath
    -- ^ Load script from file
    | ProofStatus
    -- ^ Show proof status of each claim
    | Log Logger.Severity LogScope LogType
    -- ^ Setup the Kore logger.
    | Exit
    -- ^ Exit the repl.
    deriving (Eq, Show)

commandSet :: Set String
commandSet = Set.fromList
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
    \help                                  shows this help message\n\
    \claim [n|<name>]                      shows the nth claim, the claim with\
                                           \ <name> or if used without args\
                                           \ shows the currently focused claim\n\
    \axiom <n|name>                        shows the nth axiom or the axiom\
                                           \ with <name>\n\
    \prove <n|name>                        initializes proof mode for the nth\
                                           \ claim or for the claim with <name>\n\
    \graph [file]                          shows the current proof graph (*)(**)\n\
    \                                      (saves image in .jpeg format if file\
                                           \ argument is given; file extension\
                                           \ is added automatically)\n\
    \step [n]                              attempts to run 'n' proof steps at\
                                           \the current node (n=1 by default)\n\
    \stepf [n]                             attempts to run 'n' proof steps at\
                                           \ the current node, stepping through\
                                           \ branchings (n=1 by default)\n\
    \select <n>                            select node id 'n' from the graph\n\
    \config [n]                            shows the config for node 'n'\
                                           \ (defaults to current node)\n\
    \omit [cell]                           adds or removes cell to omit list\
                                           \ (defaults to showing the omit\
                                           \ list)\n\
    \leafs                                 shows unevaluated or stuck leafs\n\
    \rule [n]                              shows the rule for node 'n'\
                                           \ (defaults to current node)\n\
    \prec-branch [n]                       shows first preceding branch\
                                           \ (defaults to current node)\n\
    \children [n]                          shows direct children of node\
                                           \ (defaults to current node)\n\
    \label                                 shows all node labels\n\
    \label <l>                             jump to a label\n\
    \label <+l> [n]                        add a new label for a node\
                                           \ (defaults to current node)\n\
    \label <-l>                            remove a label\n\
    \try (<a|c><num>)|<name>               attempts <a>xiom or <c>laim at\
                                           \ index <num> or rule with <name>\n\
    \tryf (<a|c><num>)|<name>              attempts <a>xiom or <c>laim at\
                                           \ index <num> or rule with <name>,\
                                           \ and if successful, it will apply it.\n\
    \clear [n]                             removes all node children from the\
                                           \ proof graph\n\
    \                                      (defaults to current node)\n\
    \save-session file                     saves the current session to file\n\
    \alias <name> = <command>              adds as an alias for <command>\n\
    \<alias>                               runs an existing alias\n\
    \load file                             loads the file as a repl script\n\
    \proof-status                          shows status for each claim\n\
    \log <severity> [<scope>] <type>       configures the logging output\n\
    \                                      <severity> can be debug, info,\
                                           \ warning, error, or critical\n\
    \                                      [<scope>] is the list of scopes\
                                           \ separated by white spaces or\
                                           \ commas, e.g. '[scope1, scope2]';\n\
    \                                      these scopes are used for filtering\
                                           \ the logged information, for example,\
                                           \ '[]' will log all scopes\n\
    \                                      <type> can be 'none', 'stdout',\
                                           \ or 'file filename'\n\
    \exit                                  exits the repl\
    \\n\n\
    \Available modifiers:\n\
    \<command> > file                      prints the output of 'command'\
                                           \ to file\n\
    \<command> >> file                     appends the output of 'command'\
                                           \ to file\n\
    \<command> | external script           pipes command to external script\
                                           \ and prints the result in the\
                                           \ repl\n\
    \<command> | external script > file    pipes and then redirects the output\
                                           \ of the piped command to a file\n\
    \<command> | external script >> file   pipes and then appends the output\
                                           \ of the piped command to a file\n\
    \\n\
    \(*) If an edge is labeled as Simpl/RD it means that either the target node\n\
    \ was reached using the SMT solver or it was reached through the Remove \n\
    \ Destination step.\n\
    \(**) A green node represents the proof has completed on\
    \ that respective branch.\
    \\n\n\
    \Rule names can be added in two ways:\n\
    \    a) rule <k> ... </k> [label(myName)]\n\
    \    b) rule [myName] : <k> ... </k>\n\
    \Names added via a) can be used as-is. Note that names which match the\n\
    \ indexing syntax for the try and tryf commands shouldn't be added\n\
    \ (e.g. a5 as a rule name).\n\
    \Names added via b) need to be prefixed with the module name followed by\n\
    \ dot, e.g. IMP.myName"

-- | Determines whether the command needs to be stored or not. Commands that
-- affect the outcome of the proof are stored.
shouldStore :: ReplCommand -> Bool
shouldStore =
    \case
        ShowUsage        -> False
        Help             -> False
        ShowClaim _      -> False
        ShowAxiom _      -> False
        ShowGraph _      -> False
        ShowConfig _     -> False
        ShowLeafs        -> False
        ShowRule _       -> False
        ShowPrecBranch _ -> False
        ShowChildren _   -> False
        SaveSession _    -> False
        ProofStatus      -> False
        Try _            -> False
        Exit             -> False
        _                -> True

-- Type synonym for the actual type of the execution graph.
type ExecutionGraph rule =
    Strategy.ExecutionGraph
        CommonProofState
        rule

type InnerGraph rule =
    Gr CommonProofState (Seq rule)

-- | State for the repl.
data ReplState claim = ReplState
    { axioms     :: [Rule claim]
    -- ^ List of available axioms
    , claims     :: [claim]
    -- ^ List of claims to be proven
    , claim      :: claim
    -- ^ Currently focused claim in the repl
    , claimIndex :: ClaimIndex
    -- ^ Index of the currently focused claim in the repl
    , graphs     :: Map ClaimIndex (ExecutionGraph (Rule claim))
    -- ^ Execution graph for the current proof; initialized with root = claim
    , node       :: ReplNode
    -- ^ Currently selected node in the graph; initialized with node = root
    , commands   :: Seq String
    -- ^ All commands evaluated by the current repl session
    , omit       :: Set String
    -- ^ The omit list, initially empty
    , labels  :: Map ClaimIndex (Map String ReplNode)
    -- ^ Map from labels to nodes
    , aliases :: Map String AliasDefinition
    -- ^ Map of command aliases
    , logging :: (Logger.Severity, LogScope, LogType)
    -- ^ The log level, log scopes and log type decide what gets logged and where.
    }
    deriving (GHC.Generic)

-- | Configuration environment for the repl.
data Config claim m = Config
    { stepper
        :: claim
        -> [claim]
        -> [Rule claim]
        -> ExecutionGraph (Rule claim)
        -> ReplNode
        -> m (ExecutionGraph (Rule claim))
    -- ^ Stepper function, it is a partially applied 'verifyClaimStep'
    , unifier
        :: TermLike Variable
        -> TermLike Variable
        -> UnifierWithExplanation m (IPredicate.Predicate Variable)
    -- ^ Unifier function, it is a partially applied 'unificationProcedure'
    --   where we discard the result since we are looking for unification
    --   failures
    , logger  :: MVar (Logger.LogAction IO Logger.SomeEntry)
    -- ^ Logger function, see 'logging'.
    , outputFile :: OutputFile
    -- ^ Output resulting pattern to this file.
    }
    deriving (GHC.Generic)

-- | Unifier that stores the first 'explainBottom'.
-- See 'runUnifierWithExplanation'.
newtype UnifierWithExplanation m a =
    UnifierWithExplanation
        { getUnifierWithExplanation
            :: UnifierT (AccumT (First ReplOutput) m) a
        }
  deriving (Alternative, Applicative, Functor, Monad)

deriving instance MonadSMT m => MonadSMT (UnifierWithExplanation m)

deriving instance MonadProfiler m => MonadProfiler (UnifierWithExplanation m)

instance Logger.WithLog Logger.LogMessage m
    => Logger.WithLog Logger.LogMessage (UnifierWithExplanation m)
  where
    askLogAction =
        Logger.hoistLogAction UnifierWithExplanation
        <$> UnifierWithExplanation Logger.askLogAction
    {-# INLINE askLogAction #-}

    localLogAction locally =
        UnifierWithExplanation
        . Logger.localLogAction locally
        . getUnifierWithExplanation
    {-# INLINE localLogAction #-}

deriving instance MonadSimplify m => MonadSimplify (UnifierWithExplanation m)

instance MonadSimplify m => MonadUnify (UnifierWithExplanation m) where
    throwSubstitutionError =
        UnifierWithExplanation . Monad.Unify.throwSubstitutionError
    throwUnificationError =
        UnifierWithExplanation . Monad.Unify.throwUnificationError

    gather =
        UnifierWithExplanation . Monad.Unify.gather . getUnifierWithExplanation
    scatter = UnifierWithExplanation . Monad.Unify.scatter

    explainBottom info first second =
        UnifierWithExplanation
        . Monad.Trans.lift
        . Monad.Accum.add
        . First
        . Just $ ReplOutput
            [ AuxOut . show $ info <> "\n"
            , AuxOut "When unifying:\n"
            , KoreOut $ (show . Pretty.indent 4 . unparse $ first) <> "\n"
            , AuxOut "With:\n"
            , KoreOut $ (show . Pretty.indent 4 . unparse $ second) <> "\n"
            ]

-- | Result after running one or multiple proof steps.
data StepResult
    = NoResult
    -- ^ reached end of proof on current branch
    | SingleResult ReplNode
    -- ^ single follow-up configuration
    | BranchResult [ReplNode]
    -- ^ configuration branched
    deriving (Show)

data NodeState = StuckNode | UnevaluatedNode
    deriving (Eq, Ord, Show)

data AliasError
    = NameAlreadyDefined
    | UnknownCommand

data GraphProofStatus
    = NotStarted
    | Completed
    | InProgress [Graph.Node]
    | StuckProof [Graph.Node]
    | TrustedClaim
    deriving (Eq, Show)

makeAuxReplOutput :: String -> ReplOutput
makeAuxReplOutput str =
    ReplOutput . return . AuxOut $ str <> "\n"

makeKoreReplOutput :: String -> ReplOutput
makeKoreReplOutput str =
    ReplOutput . return . KoreOut $ str <> "\n"

runUnifierWithExplanation
    :: forall m a
    .  MonadSimplify m
    => UnifierWithExplanation m a
    -> m (Either ReplOutput (NonEmpty a))
runUnifierWithExplanation (UnifierWithExplanation unifier) =
    either explainError failWithExplanation <$> unificationResults
  where
    unificationResults
        ::  m (Either UnificationOrSubstitutionError ([a], First ReplOutput))
    unificationResults =
        fmap (\(r, ex) -> flip (,) ex <$> r)
        . flip runAccumT mempty
        . Monad.Unify.runUnifierT
        $ unifier
    explainError = Left . makeAuxReplOutput . show . Pretty.pretty
    failWithExplanation
        :: ([a], First ReplOutput)
        -> Either ReplOutput (NonEmpty a)
    failWithExplanation (results, explanation) =
        case results of
            [] ->
                Left $ fromMaybe
                    (makeAuxReplOutput "No explanation given")
                    (getFirst explanation)
            r : rs -> Right (r :| rs)
