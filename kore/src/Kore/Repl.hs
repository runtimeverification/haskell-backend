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

import           Control.Exception
                 ( AsyncException (UserInterrupt) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad
                 ( void, when )
import           Control.Monad.Catch
                 ( MonadCatch, catch )
import           Control.Monad.Extra
                 ( whileM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.State.Strict
                 ( MonadState, StateT, evalStateT )
import           Data.Coerce
                 ( coerce )
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( listToMaybe )
import qualified Data.Sequence as Seq
import           Kore.Attribute.RuleIndex
import           System.Exit
import           System.IO
                 ( hFlush, stdout )
import           Text.Megaparsec
                 ( parseMaybe )

import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.TermLike
                 ( TermLike, Variable )
import qualified Kore.Logger as Logger
import           Kore.OnePath.Verification
                 ( verifyClaimStep )
import           Kore.OnePath.Verification
                 ( Axiom )
import           Kore.OnePath.Verification
                 ( Claim )
import           Kore.OnePath.Verification
import           Kore.Repl.Data
import           Kore.Repl.Interpreter
import           Kore.Repl.Parser
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Rule as Rule
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import           Kore.Step.Simplification.Data
                 ( TermLikeSimplifier )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier )
import qualified Kore.Step.Strategy as Strategy
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
    => SmtMetadataTools StepperAttributes
    -- ^ tools required for the proof
    -> TermLikeSimplifier
    -- ^ pattern simplifier
    -> PredicateSimplifier
    -- ^ predicate simplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ builtin simplifier
    -> [Axiom]
    -- ^ list of axioms to used in the proof
    -> [claim]
    -- ^ list of claims to be proven
    -> ReplScript
    -- ^ optional script
    -> ReplMode
    -- ^ mode to run in
    -> Simplifier ()
runRepl
    tools simplifier predicateSimplifier axiomToIdSimplifier
    axioms' claims' initScript replMode
  = do
    let mscript = unReplScript initScript
    mNewState <- maybe (pure . pure $ state) (parseEvalScript state) mscript
    case replMode of
        Interactive -> do
            replGreeting
            evalStateT (whileM repl0) (maybe state id mNewState)
        RunScript ->
            case mNewState of
                Nothing -> liftIO exitFailure
                Just newState -> do
                    -- void
                    -- $ evalStateT (replInterpreter printIfNotEmpty ProofStatus) newState
                    let pstatus = allProofs
                                    (graphs newState)
                                    (claims newState)
                                    (ClaimIndex <$> [0..length (claims newState) - 1])
                    let isCompleted = foldr (&&) True
                                        ( fmap
                                          (\x -> x == Completed)
                                          (Map.elems pstatus)
                                        )
                    liftIO . putStrLn . showProofStatus $ pstatus
                    if isCompleted == True
                       then liftIO exitSuccess
                       else liftIO . exitWith $ ExitFailure 2

  where

    repl0 :: StateT (ReplState claim) Simplifier Bool
    repl0 = do
        str <- prompt
        let command = maybe ShowUsage id $ parseMaybe commandParser str
        when (shouldStore command) $ lensCommands Lens.%= (Seq.|> str)
        replInterpreter printIfNotEmpty command

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
            , omit       = []
            , stepper    = stepper0
            , unifier    = unifier0
            , labels     = Map.empty
            , aliases    = Map.empty
            , logging    = (Logger.Debug, NoLogging)
            }

    firstClaimIndex :: ClaimIndex
    firstClaimIndex = ClaimIndex 0

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
    firstClaim = maybe (error "No claims found") id $ listToMaybe claims'

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
                $ verifyClaimStep
                    tools
                    simplifier
                    predicateSimplifier
                    axiomToIdSimplifier
                    claim
                    claims
                    axioms
                    graph
                    node
            else pure graph

    unifier0
        :: TermLike Variable
        -> TermLike Variable
        -> UnifierWithExplanation ()
    unifier0 first second =
        () <$ unificationProcedure
            tools
            predicateSimplifier
            simplifier
            axiomToIdSimplifier
            first
            second

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
