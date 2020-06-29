{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.ProofState
    ( extractGoalRem
    , extractUnproven
    , ProofState (..)
    , Prim (..)
    , proofState
    , ProofStateTransformer (..)
    ) where

import Prelude.Kore

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
    | CheckImplication
    | TriviallyValid
    | DerivePar [rule]
    | DeriveSeq [rule]
    | ApplyClaims
    deriving (Show, Functor)

instance Filterable Prim where
    mapMaybe _ CheckProven        = CheckProven
    mapMaybe _ CheckGoalRemainder = CheckGoalRemainder
    mapMaybe _ CheckGoalStuck     = CheckGoalStuck
    mapMaybe _ ResetGoal          = ResetGoal
    mapMaybe _ Simplify           = Simplify
    mapMaybe _ CheckImplication   = CheckImplication
    mapMaybe _ TriviallyValid     = TriviallyValid
    mapMaybe _ ApplyClaims        = ApplyClaims
    mapMaybe f (DerivePar rules)  = DerivePar (mapMaybe f rules)
    mapMaybe f (DeriveSeq rules)  = DeriveSeq (mapMaybe f rules)

instance Unparse goal => Pretty (Prim goal) where
    pretty CheckProven = "Transition CheckProven."
    pretty CheckGoalRemainder = "Transition CheckGoalRemainder."
    pretty CheckGoalStuck = "Transition CheckGoalStuck."
    pretty ResetGoal = "Transition ResetGoal."
    pretty Simplify = "Transition Simplify."
    pretty CheckImplication = "Transition CheckImplication."
    pretty TriviallyValid = "Transition TriviallyValid."
    pretty ApplyClaims = "apply claims"
    pretty (DerivePar rules) =
        Pretty.vsep
            $ ["Transition DerivePar with rules:"]
            <> fmap (Pretty.indent 4 . unparse) rules
    pretty (DeriveSeq rules) =
        Pretty.vsep
            $ ["Transition DeriveSeq with rules:"]
            <> fmap (Pretty.indent 4 . unparse) rules

{- | The state of the reachability proof strategy for @goal@.
 -}
data ProofState goal
    = Goal !goal
    -- ^ The indicated goal is being proven.
    | GoalRemainder !goal
    -- ^ The indicated goal remains after rewriting.
    | GoalRewritten !goal
    -- ^ We already rewrote the goal this step.
    | GoalStuck !goal
    -- ^ If the terms unify and the condition does not imply
    -- the goal, the proof is stuck. This state should be reachable
    -- only by applying CheckImplication.
    | Proven
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
    pretty (Goal goal) =
        Pretty.vsep
            ["Proof state Goal:"
            , Pretty.indent 4 $ unparse goal
            ]
    pretty (GoalRemainder goal) =
        Pretty.vsep
            ["Proof state GoalRemainder:"
            , Pretty.indent 4 $ unparse goal
            ]
    pretty (GoalRewritten goal) =
        Pretty.vsep
            ["Proof state GoalRewritten:"
            , Pretty.indent 4 $ unparse goal
            ]
    pretty (GoalStuck goal) =
        Pretty.vsep
            ["Proof state GoalStuck:"
            , Pretty.indent 4 $ unparse goal
            ]
    pretty Proven = "Proof state Proven."

{- | Extract the unproven goals of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ProofState a -> Maybe a
extractUnproven (Goal t)    = Just t
extractUnproven (GoalRewritten t) = Just t
extractUnproven (GoalRemainder t) = Just t
extractUnproven (GoalStuck t) = Just t
extractUnproven Proven      = Nothing

extractGoalRem :: ProofState a -> Maybe a
extractGoalRem (GoalRemainder t) = Just t
extractGoalRem _           = Nothing

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
        Goal goal -> goalTransformer goal
        GoalRemainder goal -> goalRemainderTransformer goal
        GoalRewritten goal -> goalRewrittenTransformer goal
        GoalStuck goal -> goalStuckTransformer goal
        Proven -> provenValue
