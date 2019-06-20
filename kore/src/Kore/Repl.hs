{-|
Module      : Kore.Repl
Description : Proof REPL
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl
    ( runRepl
    , ReplScript (..)
    , ReplMode (..)
    ) where

import           Control.Concurrent.MVar
import           Control.Exception
                 ( AsyncException (UserInterrupt) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad
                 ( forever, void, when )
import           Control.Monad.Catch
                 ( MonadCatch, catch )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.State.Strict
                 ( MonadState, StateT, evalStateT )
import           Data.Coerce
                 ( coerce )
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.List
                 ( findIndex )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import           Kore.Attribute.RuleIndex
import           System.Exit
import           System.IO
                 ( hFlush, stdout )
import           Text.Megaparsec
                 ( parseMaybe )

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Logger as Logger
import           Kore.OnePath.Verification
                 ( verifyClaimStep )
import           Kore.OnePath.Verification
                 ( Axiom, Claim, isTrusted )
import           Kore.OnePath.Verification
import           Kore.Repl.Data
import           Kore.Repl.Interpreter
import           Kore.Repl.Parser
import qualified Kore.Step.Rule as Rule
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Syntax.Variable
import           Kore.Unification.Procedure
                 ( unificationProcedure )
import           Kore.Unparser
                 ( Unparse )

-- | Represents an optional file name which contains a sequence of
-- repl commands.
newtype ReplScript = ReplScript
    { unReplScript :: Maybe FilePath
    } deriving (Eq, Show)

data ReplMode = Interactive | RunScript
    deriving (Eq, Show)

-- | Runs the repl for proof mode. It requires all the tooling and simplifiers
-- that would otherwise be required in the proof and allows for step-by-step
-- execution of proofs. Currently works via stdin/stdout interaction.
runRepl
    :: forall claim
    .  Unparse (Variable)
    => Claim claim
    => [Axiom]
    -- ^ list of axioms to used in the proof
    -> [claim]
    -- ^ list of claims to be proven
    -> MVar (Logger.LogAction IO Logger.LogMessage)
    -> ReplScript
    -- ^ optional script
    -> ReplMode
    -- ^ mode to run in
    -> Simplifier ()
runRepl axioms' claims' logger replScript replMode = do
    mNewState <- evaluateScript replScript
    case replMode of
        Interactive -> do
            replGreeting
            evalStateT (forever repl0) (maybe state id mNewState)
        RunScript ->
            case mNewState of
                Nothing -> liftIO exitFailure
                Just newState -> do
                    runReplCommand ProofStatus newState
                    runReplCommand Exit newState

  where

    runReplCommand :: ReplCommand -> ReplState claim -> Simplifier ()
    runReplCommand cmd st =
        void $ evalStateT (replInterpreter printIfNotEmpty cmd) st

    evaluateScript :: ReplScript -> Simplifier (Maybe (ReplState claim))
    evaluateScript rs =
        maybe
            (pure . pure $ state)
            (parseEvalScript state)
            (unReplScript rs)

    repl0 :: StateT (ReplState claim) Simplifier ()
    repl0 = do
        str <- prompt
        let command = maybe ShowUsage id $ parseMaybe commandParser str
        when (shouldStore command) $ lensCommands Lens.%= (Seq.|> str)
        void $ replInterpreter printIfNotEmpty command

    state :: ReplState claim
    state =
        ReplState
            { axioms     = addIndexesToAxioms axioms'
            , claims     = addIndexesToClaims (length axioms') claims'
            , claim      = firstClaim
            , claimIndex = firstClaimIndex
            , graphs     = Map.singleton firstClaimIndex firstClaimExecutionGraph
            , node       = ReplNode (Strategy.root firstClaimExecutionGraph)
            , commands   = Seq.empty
            -- TODO(Vladimir): should initialize this to the value obtained from
            -- the frontend via '--omit-labels'.
            , omit       = mempty
            , stepper    = stepper0
            , unifier    = unificationProcedure
            , labels     = Map.empty
            , aliases    = Map.empty
            , logging    = (Logger.Debug, NoLogging)
            , logger
            }

    firstClaimIndex :: ClaimIndex
    firstClaimIndex =
        ClaimIndex
        . maybe (error "No claims found") id
        $ findIndex (not . isTrusted) claims'

    addIndexesToAxioms
        :: [Axiom]
        -> [Axiom]
    addIndexesToAxioms axs =
        fmap (Axiom . addIndex) (zip (fmap unAxiom axs) [0..])

    addIndexesToClaims
        :: Int
        -> [claim]
        -> [claim]
    addIndexesToClaims len cls =
        fmap
            (coerce . Rule.getRewriteRule . addIndex)
            (zip (fmap (Rule.RewriteRule . coerce) cls) [len..])

    addIndex
        :: (Rule.RewriteRule Variable, Int)
        -> Rule.RewriteRule Variable
    addIndex (rw, n) =
        modifyAttribute (mapAttribute n (getAttribute rw)) rw

    modifyAttribute
        :: Attribute.Axiom
        -> Rule.RewriteRule Variable
        -> Rule.RewriteRule Variable
    modifyAttribute att (Rule.RewriteRule rp) =
        Rule.RewriteRule $ rp { Rule.attributes = att }

    getAttribute :: Rule.RewriteRule Variable -> Attribute.Axiom
    getAttribute = Rule.attributes . Rule.getRewriteRule

    mapAttribute :: Int -> Attribute.Axiom -> Attribute.Axiom
    mapAttribute n attr =
        Lens.over Attribute.lensIdentifier (makeRuleIndex n) attr

    makeRuleIndex :: Int -> RuleIndex -> RuleIndex
    makeRuleIndex n _ = RuleIndex (Just n)

    firstClaim :: Claim claim => claim
    firstClaim =
        claims' !! unClaimIndex firstClaimIndex

    firstClaimExecutionGraph :: ExecutionGraph
    firstClaimExecutionGraph = emptyExecutionGraph firstClaim

    stepper0
        :: claim
        -> [claim]
        -> [Axiom]
        -> ExecutionGraph
        -> ReplNode
        -> Simplifier ExecutionGraph
    stepper0 claim claims axioms graph rnode = do
        let node = unReplNode rnode
        if Graph.outdeg (Strategy.graph graph) node == 0
            then
                catchInterruptWithDefault graph
                $ verifyClaimStep claim claims axioms graph node
            else pure graph

    catchInterruptWithDefault :: MonadCatch m => MonadIO m => a -> m a -> m a
    catchInterruptWithDefault def sa =
        catch sa $ \UserInterrupt -> do
            liftIO $ putStrLn "Step evaluation interrupted."
            pure def

    replGreeting :: MonadIO m => m ()
    replGreeting =
        liftIO $
            putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

    prompt :: MonadIO m => MonadState (ReplState claim) m => m String
    prompt = do
        node <- Lens.use lensNode
        liftIO $ do
            putStr $ "Kore (" <> show (unReplNode node) <> ")> "
            hFlush stdout
            getLine
