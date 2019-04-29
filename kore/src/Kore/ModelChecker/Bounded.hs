{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.ModelChecker.Bounded
    ( CheckResult (..)
    , bmcStrategy
    , check
    ) where

import qualified Data.Foldable as Foldable
import           Data.Limit
                 ( Limit )
import qualified Data.Limit as Limit
import           Debug.Trace

import           Kore.AST.Common
                 ( SymbolOrAlias (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.ModelChecker.Step
                 ( CommonModalPattern, CommonProofState, ModalPattern (..),
                 Prim (..), defaultOneStepStrategy )
import qualified Kore.ModelChecker.Step as ProofState
                 ( ProofState (..) )
import qualified Kore.ModelChecker.Step as ModelChecker
                 ( transitionRule )
import           Kore.OnePath.Verification
                 ( Axiom (Axiom) )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern
                 ( Conditional (Conditional) )
import           Kore.Step.Pattern as Conditional
                 ( Conditional (..) )
import           Kore.Step.Rule
                 ( ImplicationRule (ImplicationRule), RewriteRule,
                 RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import           Kore.Step.Strategy
                 ( Strategy, TransitionT, pickFinal, runStrategy )
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
    -> TermLikeSimplifier Object
    -- ^ Simplifies normal patterns through, e.g., function evaluation
    -> PredicateSimplifier Object
    -- ^ Simplifies predicates
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    ->  (  CommonModalPattern Object
        -> [Strategy
            (Prim
                (CommonModalPattern Object)
                (RewriteRule Object Variable)
            )
           ]
        )
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> [(ImplicationRule Object Variable, Limit Natural)]
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> Simplifier [CheckResult]
check
    metadataTools
    simplifier
    substitutionSimplifier
    axiomIdToSimplifier
    strategyBuilder
  =
    mapM
        (checkClaim
            metadataTools
            simplifier
            substitutionSimplifier
            axiomIdToSimplifier
            strategyBuilder
        )

bmcStrategy
    :: [Axiom Object]
    -> CommonModalPattern Object
    -> [Strategy
        (Prim
            (CommonModalPattern Object)
            (RewriteRule Object Variable)
        )
       ]
bmcStrategy
    axioms
    goal
  =  repeat (defaultOneStepStrategy goal rewrites)
  where
    rewrites :: [RewriteRule Object Variable]
    rewrites = map unwrap axioms
      where
        unwrap (Axiom a) = a

checkClaim
    :: SmtMetadataTools StepperAttributes
    -> TermLikeSimplifier Object
    -> PredicateSimplifier Object
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from symbol IDs to defined functions
    ->  (  CommonModalPattern Object
        -> [Strategy
            (Prim
                (CommonModalPattern Object)
                (RewriteRule Object Variable)
            )
           ]
        )
    -> (ImplicationRule Object Variable, Limit Natural)
    -> Simplifier CheckResult
checkClaim
    metadataTools
    simplifier
    substitutionSimplifier
    axiomIdToSimplifier
    strategyBuilder
    (ImplicationRule RulePattern { left, right }, stepLimit)
  = do
        let
            App_ SymbolOrAlias { symbolOrAliasConstructor = symbol } [prop] = right
            goalPattern = ModalPattern { modalOp = getId symbol, term = prop }
            strategy =
                Limit.takeWithin
                    stepLimit
                    (strategyBuilder goalPattern)
            startState :: CommonProofState Object
            startState =
                ProofState.GoalLHS
                    Conditional
                        {term = left, predicate = Predicate.makeTruePredicate, substitution = mempty}
        executionGraph <- runStrategy transitionRule' strategy startState
        let
            finalResult = (checkFinalNodes . pickFinal) executionGraph
        trace (show finalResult) (return finalResult)
  where
    transitionRule'
        :: Prim (CommonModalPattern Object) (RewriteRule Object Variable)
        -> (CommonProofState Object)
        -> TransitionT (RewriteRule Object Variable) Simplifier
            (CommonProofState Object)
    transitionRule' =
        ModelChecker.transitionRule
            metadataTools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier

    checkFinalNodes
        :: [CommonProofState Object]
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
