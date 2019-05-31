{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.ModelChecker.Bounded
    ( CheckResult (..)
    , bmcStrategy
    , check
    ) where

import qualified Control.Monad.State.Strict as State
import qualified Data.Foldable as Foldable
import           Data.Limit
                 ( Limit )
import qualified Data.Limit as Limit
import           Debug.Trace

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Pattern
                 ( Conditional (Conditional) )
import           Kore.Internal.Pattern as Conditional
                 ( Conditional (..) )
import           Kore.Internal.TermLike
import           Kore.ModelChecker.Step
                 ( CommonModalPattern, CommonProofState, ModalPattern (..),
                 Prim (..), defaultOneStepStrategy )
import qualified Kore.ModelChecker.Step as ProofState
                 ( ProofState (..) )
import qualified Kore.ModelChecker.Step as ModelChecker
                 ( Transition, transitionRule )
import           Kore.OnePath.Verification
                 ( Axiom (Axiom) )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Rule
                 ( ImplicationRule (ImplicationRule), RewriteRule,
                 RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import           Kore.Step.Strategy
                 ( GraphSearchOrder, Strategy, pickFinal,
                 runStrategyWithSearchOrder )
import           Kore.Syntax.Application
                 ( SymbolOrAlias (..) )
import           Kore.Syntax.Id
                 ( Id (..) )
import           Kore.Syntax.Variable
                 ( Variable )
import           Numeric.Natural
                 ( Natural )

data CheckResult
    = Proved
    -- ^ Property is proved within the bound.
    | Failed
    -- ^ Counter example is found within the bound.
    | Unknown
    -- ^ Result is unknown within the bound.
    deriving (Show)

check
    :: SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier
    -- ^ Simplifies normal patterns through, e.g., function evaluation
    -> PredicateSimplifier
    -- ^ Simplifies predicates
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    ->  (  CommonModalPattern
        -> [Strategy
            (Prim
                (CommonModalPattern)
                (RewriteRule Variable)
            )
           ]
        )
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> GraphSearchOrder
    -> [(ImplicationRule Variable, Limit Natural)]
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> Simplifier [CheckResult]
check
    metadataTools
    simplifier
    substitutionSimplifier
    axiomIdToSimplifier
    strategyBuilder
    searchOrder
  =
    mapM
        (checkClaim
            metadataTools
            simplifier
            substitutionSimplifier
            axiomIdToSimplifier
            strategyBuilder
            searchOrder
        )

bmcStrategy
    :: [Axiom]
    -> CommonModalPattern
    -> [Strategy
        (Prim
            (CommonModalPattern)
            (RewriteRule Variable)
        )
       ]
bmcStrategy
    axioms
    goal
  =  repeat (defaultOneStepStrategy goal rewrites)
  where
    rewrites :: [RewriteRule Variable]
    rewrites = map unwrap axioms
      where
        unwrap (Axiom a) = a

checkClaim
    :: SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier
    -> PredicateSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    ->  (  CommonModalPattern
        -> [Strategy
            (Prim
                (CommonModalPattern)
                (RewriteRule Variable)
            )
           ]
        )
    -> GraphSearchOrder
    -> (ImplicationRule Variable, Limit Natural)
    -> Simplifier CheckResult
checkClaim
    _metadataTools
    simplifier
    substitutionSimplifier
    axiomIdToSimplifier
    strategyBuilder
    searchOrder
    (ImplicationRule RulePattern { left, right }, stepLimit)
  = do
        let
            App_ SymbolOrAlias
                { symbolOrAliasConstructor = symbol } [prop]
              = right
            goalPattern = ModalPattern { modalOp = getId symbol, term = prop }
            strategy =
                Limit.takeWithin
                    stepLimit
                    (strategyBuilder goalPattern)
            startState :: CommonProofState
            startState =
                ProofState.GoalLHS
                    Conditional
                        { term = left
                        , predicate = Predicate.makeTruePredicate
                        , substitution = mempty
                        }
        executionGraph <- State.evalStateT
                            (runStrategyWithSearchOrder
                                transitionRule'
                                strategy
                                searchOrder
                                startState)
                            Nothing
        let
            finalResult = (checkFinalNodes . pickFinal) executionGraph
        trace (show finalResult) (return finalResult)
  where
    transitionRule'
        :: Prim (CommonModalPattern) (RewriteRule Variable)
        -> (CommonProofState)
        -> ModelChecker.Transition (CommonProofState)
    transitionRule' =
        ModelChecker.transitionRule
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier

    checkFinalNodes
        :: [CommonProofState]
        -> CheckResult
    checkFinalNodes nodes
      = Foldable.foldl' checkFinalNodesHelper Proved nodes
      where
        checkFinalNodesHelper Proved  ProofState.Proven = Proved
        checkFinalNodesHelper Proved  ProofState.Unprovable = Failed
        checkFinalNodesHelper Proved  _ = Unknown
        checkFinalNodesHelper Unknown ProofState.Unprovable = Failed
        checkFinalNodesHelper Unknown _ = Unknown
        checkFinalNodesHelper Failed  _ = Failed
