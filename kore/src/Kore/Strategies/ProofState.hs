{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.ProofState
    ( extractGoalRem
    , extractUnproven
    , depth0
    , extractDepth
    , Depth (..)
    , ProofState (..)
    , Prim (..)
    , proofState
    , ProofStateTransformer (..)
    ) where

import Prelude.Kore

import Numeric.Natural
    ( Natural
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

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
data Prim rule
    = CheckProven
    -- ^ End execution on this branch if the state is 'Proven'.
    | CheckGoalRemainder
    -- ^ End execution on this branch if the state is 'GoalRemainder'.
    | CheckGoalStuck
    -- ^ End execution on this branch immediately if the state is 'GoalStuck'.
    | ResetGoal
    -- ^ Mark all goals rewritten previously as new goals.
    | Simplify
    | RemoveDestination
    | TriviallyValid
    | DerivePar [rule]
    | DeriveSeq [rule]
    deriving (Show, Functor)

instance Filterable Prim where
    mapMaybe _ CheckProven        = CheckProven
    mapMaybe _ CheckGoalRemainder = CheckGoalRemainder
    mapMaybe _ CheckGoalStuck     = CheckGoalStuck
    mapMaybe _ ResetGoal          = ResetGoal
    mapMaybe _ Simplify           = Simplify
    mapMaybe _ RemoveDestination  = RemoveDestination
    mapMaybe _ TriviallyValid     = TriviallyValid
    mapMaybe f (DerivePar rules)  = DerivePar (mapMaybe f rules)
    mapMaybe f (DeriveSeq rules)  = DeriveSeq (mapMaybe f rules)

instance Unparse goal => Pretty (Prim goal) where
    pretty CheckProven = "Transition CheckProven."
    pretty CheckGoalRemainder = "Transition CheckGoalRemainder."
    pretty CheckGoalStuck = "Transition CheckGoalStuck."
    pretty ResetGoal = "Transition ResetGoal."
    pretty Simplify = "Transition Simplify."
    pretty RemoveDestination = "Transition RemoveDestination."
    pretty TriviallyValid = "Transition TriviallyValid."
    pretty (DerivePar rules) =
        Pretty.vsep
            $ ["Transition DerivePar with rules:"]
            <> fmap (Pretty.indent 4 . unparse) rules
    pretty (DeriveSeq rules) =
        Pretty.vsep
            $ ["Transition DeriveSeq with rules:"]
            <> fmap (Pretty.indent 4 . unparse) rules

newtype Depth = Depth { getDepth :: Natural}
    deriving (Eq, Show, Ord, Hashable, Debug, Diff)

depth0 :: Depth
depth0 = Depth 0

{- | The state of the reachability proof strategy for @goal@.
 -}
data ProofState goal
    = Goal Depth !goal
    -- ^ The indicated goal is being proven.
    | GoalRemainder Depth !goal
    -- ^ The indicated goal remains after rewriting.
    | GoalRewritten Depth !goal
    -- ^ We already rewrote the goal this step.
    | GoalStuck Depth !goal
    -- ^ If the terms unify and the condition does not imply
    -- the goal, the proof is stuck. This state should be reachable
    -- only by applying RemoveDestination.
    | Proven Depth
    -- ^ The parent goal was proven.
    deriving (Eq, Show, Ord, Functor, GHC.Generic)

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
    pretty (Proven depth) =
        Pretty.vsep
            ["Proof state Proven."
            , Pretty.hsep ["Depth:", Pretty.pretty (getDepth depth)]
            ]

{- | Extract the unproven goals of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ProofState a -> Maybe a
extractUnproven (Goal _ t)    = Just t
extractUnproven (GoalRewritten _ t) = Just t
extractUnproven (GoalRemainder _ t) = Just t
extractUnproven (GoalStuck _ t) = Just t
extractUnproven (Proven _)      = Nothing

extractGoalRem :: ProofState a -> Maybe a
extractGoalRem (GoalRemainder _ t) = Just t
extractGoalRem _           = Nothing

extractDepth :: ProofState a -> Depth
extractDepth (Goal d _)    = d
extractDepth (GoalRewritten d _) = d
extractDepth (GoalRemainder d _) = d
extractDepth (GoalStuck d _) = d
extractDepth (Proven d)      = d

data ProofStateTransformer a val =
    ProofStateTransformer
        { goalTransformer :: a -> val
        , goalRemainderTransformer :: a -> val
        , goalRewrittenTransformer :: a -> val
        , goalStuckTransformer :: a -> val
        , provenValue :: val
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
        Goal _ goal -> goalTransformer goal
        GoalRemainder _ goal -> goalRemainderTransformer goal
        GoalRewritten _ goal -> goalRewrittenTransformer goal
        GoalStuck _ goal -> goalStuckTransformer goal
        Proven _ -> provenValue
