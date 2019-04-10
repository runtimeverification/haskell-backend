{-|
Module      : Kore.Repl
Description : Proof REPL
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Repl
    ( runRepl
    ) where

import           Control.Exception
                 ( AsyncException (UserInterrupt) )
import qualified Control.Lens as Lens hiding
                 ( makeLenses )
import           Control.Monad.Catch
                 ( MonadCatch, catch )
import           Control.Monad.Extra
                 ( whileM )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import           Control.Monad.State.Strict
                 ( MonadState, StateT, evalStateT )
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Map.Strict as Map
import           Data.Maybe
                 ( listToMaybe )
import           Kore.Attribute.RuleIndex
import           System.IO
                 ( hFlush, stdout )
import           Text.Megaparsec
                 ( parseMaybe )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
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
                 ( StepPatternSimplifier )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier )
import qualified Kore.Step.Strategy as Strategy

-- | Runs the repl for proof mode. It requires all the tooling and simplifiers
-- that would otherwise be required in the proof and allows for step-by-step
-- execution of proofs. Currently works via stdin/stdout interaction.
runRepl
    :: forall level
    .  MetaOrObject level
    => MetadataTools level StepperAttributes
    -- ^ tools required for the proof
    -> StepPatternSimplifier level
    -- ^ pattern simplifier
    -> PredicateSubstitutionSimplifier level
    -- ^ predicate simplifier
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ builtin simplifier
    -> [Axiom level]
    -- ^ list of axioms to used in the proof
    -> [Claim level]
    -- ^ list of claims to be proven
    -> Simplifier ()
runRepl tools simplifier predicateSimplifier axiomToIdSimplifier axioms' claims'
  = do
    replGreeting
    evalStateT (whileM repl0) state

  where
    repl0 :: StateT (ReplState level) Simplifier Bool
    repl0 = do
        command <- maybe ShowUsage id . parseMaybe commandParser <$> prompt
        replInterpreter putStrLn command

    state :: ReplState level
    state =
        ReplState
            { axioms  = addIndexesToAxioms axioms'
            , claims  = addIndexesToClaims axioms' claims'
            , claim   = firstClaim
            , graph   = firstClaimExecutionGraph
            , node    = (Strategy.root firstClaimExecutionGraph)
            -- TODO(Vladimir): should initialize this to the value obtained from
            -- the frontend via '--omit-labels'.
            , omit    = []
            , stepper = stepper0
            , labels  = Map.empty
            }

    addIndexesToAxioms
        :: [Axiom level]
        -> [Axiom level]
    addIndexesToAxioms axs =
        fmap (Axiom . addIndex) (zip (fmap unAxiom axs) [0..(length axs)])

    addIndexesToClaims
        :: [Axiom level]
        -> [Claim level]
        -> [Claim level]
    addIndexesToClaims axs cls =
        fmap (\(x, y) -> Claim x y)
            (zip (fmap addIndex
                    (zip (fmap rule cls)
                         [(length axs)..(length cls)] ))
                 (fmap attributes cls))

    addIndex
        :: (Rule.RewriteRule level Variable, Int)
        -> Rule.RewriteRule level Variable
    addIndex (rw, n) =
        modifyAttribute (mapAttribute n (getAttribute rw)) rw

    modifyAttribute
        :: Attribute.Axiom
        -> Rule.RewriteRule level Variable
        -> Rule.RewriteRule level Variable
    modifyAttribute att (Rule.RewriteRule rp) =
        Rule.RewriteRule $ rp { Rule.attributes = att }

    getAttribute :: Rule.RewriteRule level Variable -> Attribute.Axiom
    getAttribute = Rule.attributes . Rule.getRewriteRule

    mapAttribute :: Int -> Attribute.Axiom -> Attribute.Axiom
    mapAttribute n attr =
        Lens.over Attribute.lensIdentifier (makeRuleIndex n) attr

    makeRuleIndex :: Int -> RuleIndex -> RuleIndex
    makeRuleIndex n _ = RuleIndex (Just n)

    firstClaim :: Claim level
    firstClaim = maybe (error "No claims found") id $ listToMaybe claims'

    firstClaimExecutionGraph :: ExecutionGraph
    firstClaimExecutionGraph = emptyExecutionGraph firstClaim

    stepper0
        :: Claim level
        -> [Claim level]
        -> [Axiom level]
        -> ExecutionGraph
        -> Graph.Node
        -> Simplifier ExecutionGraph
    stepper0 claim claims axioms graph node = do
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

    catchInterruptWithDefault :: MonadCatch m => MonadIO m => a -> m a -> m a
    catchInterruptWithDefault def sa =
        catch sa $ \UserInterrupt -> do
            liftIO $ putStrLn "Step evaluation interrupted."
            pure def

    replGreeting :: MonadIO m => m ()
    replGreeting =
        liftIO $
            putStrLn "Welcome to the Kore Repl! Use 'help' to get started.\n"

    prompt :: MonadIO m => MonadState (ReplState level) m => m String
    prompt = do
        node <- Lens.use lensNode
        liftIO $ do
            putStr $ "Kore (" <> show node <> ")> "
            hFlush stdout
            getLine
