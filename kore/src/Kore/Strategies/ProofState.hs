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

import Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug


{- | The primitive transitions of the all-path reachability proof strategy.
 -}
data Prim rule
    = CheckProven
    -- ^ End execution on this branch if the state is 'Proven'.
    | CheckGoalRemainder
    -- ^ End execution on this branch if the state is 'GoalRemainder'.
    | ResetGoal
    -- ^ Mark all goals rewritten previously as new goals.
    | Simplify
    | RemoveDestination
    | TriviallyValid
    | DerivePar [rule]
    | DeriveSeq [rule]
    deriving (Show)

{- | The state of the all-path reachability proof strategy for @goal@.
 -}
data ProofState a
    = Goal a
    -- ^ The indicated goal is being proven.
    | GoalRemainder a
    -- ^ The indicated goal remains after rewriting.
    | GoalRewritten a
    -- ^ We already rewrote the goal this step.
    | Proven
    -- ^ The parent goal was proven.
    deriving (Eq, Show, Ord, Functor, GHC.Generic)

instance Hashable goal => Hashable (ProofState goal)

instance SOP.Generic (ProofState a)

instance SOP.HasDatatypeInfo (ProofState a)

instance Debug a => Debug (ProofState a)

instance (Debug a, Diff a) => Diff (ProofState a)

{- | Extract the unproven goals of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ProofState a -> Maybe a
extractUnproven (Goal t)    = Just t
extractUnproven (GoalRewritten t) = Just t
extractUnproven (GoalRemainder t) = Just t
extractUnproven Proven      = Nothing

extractGoalRem :: ProofState a -> Maybe a
extractGoalRem (GoalRemainder t) = Just t
extractGoalRem _           = Nothing

data ProofStateTransformer a val =
    ProofStateTransformer
        { goalTransformer :: a -> val
        , goalRemainderTransformer :: a -> val
        , goalRewrittenTransformer :: a -> val
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
        , provenValue
        }
  =
    \case
        Goal goal -> goalTransformer goal
        GoalRemainder goal -> goalRemainderTransformer goal
        GoalRewritten goal -> goalRewrittenTransformer goal
        Proven -> provenValue
