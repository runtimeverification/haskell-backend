{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.ProofState
    ( extractGoalRem
    , extractUnproven
    , extractDepth
    , ExecutionDepth (..)
    , increment
    , ProofState (..)
    , Prim (..)
    , proofState
    , incrementDepth
    , changeDepth
    , ProofStateTransformer (..)
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Numeric.Natural
    ( Natural
    )

import Kore.Debug
import Kore.Unparser
    ( Unparse (..)
    )
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

{- | The primitive transitions of the reachability proof strategy.
 -}
data Prim
    = CheckProven
    -- ^ End execution on this branch if the state is 'Proven'.
    | CheckGoalRemainder
    -- ^ End execution on this branch if the state is 'GoalRemainder'.
    | CheckGoalStuck
    -- ^ End execution on this branch immediately if the state is 'GoalStuck'.
    | ResetGoal
    -- ^ Mark all goals rewritten previously as new goals.
    | Simplify
    | CheckImplication
    -- ^ Check if the claim's implication is valid.
    | InferDefined
    -- ^ Infer that the left-hand side of the claim is defined. This is related
    -- to 'CheckImplication', but separated as an optimization.
    | TriviallyValid
    | ApplyClaims
    | ApplyAxioms
    deriving (Show, Eq)

instance Pretty Prim where
    pretty CheckProven = "Transition CheckProven."
    pretty CheckGoalRemainder = "Transition CheckGoalRemainder."
    pretty CheckGoalStuck = "Transition CheckGoalStuck."
    pretty ResetGoal = "Transition ResetGoal."
    pretty Simplify = "Transition Simplify."
    pretty CheckImplication = "Transition CheckImplication."
    pretty InferDefined = "infer left-hand side is defined"
    pretty TriviallyValid = "Transition TriviallyValid."
    pretty ApplyClaims = "apply claims"
    pretty ApplyAxioms = "apply axioms"

newtype ExecutionDepth = ExecutionDepth { getDepth :: Natural}
    deriving (Eq, Show, Ord, Hashable, Debug, Diff)

increment :: ExecutionDepth -> ExecutionDepth
increment (ExecutionDepth d) = ExecutionDepth (d + 1)

{- | The state of the reachability proof strategy for @goal@.
 -}
data ProofState goal
    = Goal ExecutionDepth !goal
    -- ^ The indicated goal is being proven.
    | GoalRemainder ExecutionDepth !goal
    -- ^ The indicated goal remains after rewriting.
    | GoalRewritten ExecutionDepth !goal
    -- ^ We already rewrote the goal this step.
    | GoalStuck ExecutionDepth !goal
    -- ^ If the terms unify and the condition does not imply
    -- the goal, the proof is stuck. This state should be reachable
    -- only by applying CheckImplication.
    | Proven ExecutionDepth
    -- ^ The parent goal was proven.
    deriving (Eq, Show, Ord)
    deriving (Foldable, Functor)
    deriving (GHC.Generic)

instance Hashable goal => Hashable (ProofState goal)

instance SOP.Generic (ProofState a)

instance SOP.HasDatatypeInfo (ProofState a)

instance Debug a => Debug (ProofState a)

instance (Debug a, Diff a) => Diff (ProofState a)

instance Unparse goal => Pretty (ProofState goal) where
    pretty (Goal depth goal) =
        Pretty.vsep
            ["Proof state Goal:"
            , Pretty.indent 4 $ unparse goal
            , Pretty.hsep ["Depth:", Pretty.pretty (getDepth depth)]
            ]
    pretty (GoalRemainder depth goal) =
        Pretty.vsep
            ["Proof state GoalRemainder:"
            , Pretty.indent 4 $ unparse goal
            , Pretty.hsep ["Depth:", Pretty.pretty (getDepth depth)]
            ]
    pretty (GoalRewritten depth goal) =
        Pretty.vsep
            ["Proof state GoalRewritten:"
            , Pretty.indent 4 $ unparse goal
            , Pretty.hsep ["Depth:", Pretty.pretty (getDepth depth)]
            ]
    pretty (GoalStuck depth goal) =
        Pretty.vsep
            ["Proof state GoalStuck:"
            , Pretty.indent 4 $ unparse goal
            , Pretty.hsep ["Depth:", Pretty.pretty (getDepth depth)]
            ]
    pretty (Proven _) = "Proof state Proven."

{- | Extract the unproven goals of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ProofState a -> Maybe a
extractUnproven (Goal _ t)          = Just t
extractUnproven (GoalRewritten _ t) = Just t
extractUnproven (GoalRemainder _ t) = Just t
extractUnproven (GoalStuck _ t)     = Just t
extractUnproven (Proven _)            = Nothing

extractGoalRem :: ProofState a -> Maybe a
extractGoalRem (GoalRemainder _ t) = Just t
extractGoalRem _                   = Nothing

extractDepth :: ProofState a -> ExecutionDepth
extractDepth (Goal d _)    = d
extractDepth (GoalRewritten d _) = d
extractDepth (GoalRemainder d _) = d
extractDepth (GoalStuck d _) = d
extractDepth (Proven d)      = d

incrementDepth :: ProofState a -> ProofState a
incrementDepth = changeDepth increment

changeDepth
    :: (ExecutionDepth -> ExecutionDepth)
    -> ProofState a
    -> ProofState a
changeDepth f (Goal d t)    = Goal (f d) t
changeDepth f (GoalRewritten d t) = GoalRewritten (f d) t
changeDepth f (GoalRemainder d t) = GoalRemainder (f d) t
changeDepth f (GoalStuck d t) = GoalStuck (f d) t
changeDepth f (Proven d)      = Proven (f d)

data ProofStateTransformer a val =
    ProofStateTransformer
        { goalTransformer :: ExecutionDepth -> a -> val
        , goalRemainderTransformer :: ExecutionDepth -> a -> val
        , goalRewrittenTransformer :: ExecutionDepth -> a -> val
        , goalStuckTransformer :: ExecutionDepth -> a -> val
        , provenValue :: ExecutionDepth -> val
        }

{- | Catamorphism for 'ProofState'
-}
proofState
    :: ProofStateTransformer a val
    -> ProofState a
    -> val
proofState
    ProofStateTransformer
        { goalTransformer
        , goalRemainderTransformer
        , goalRewrittenTransformer
        , goalStuckTransformer
        , provenValue
        }
  =
    \case
        Goal depth goal -> goalTransformer depth goal
        GoalRemainder depth goal -> goalRemainderTransformer depth goal
        GoalRewritten depth goal -> goalRewrittenTransformer depth goal
        GoalStuck depth goal -> goalStuckTransformer depth goal
        Proven depth -> provenValue depth
