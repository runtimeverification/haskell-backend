{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.ProofState
    ( extractGoalRem
    , extractUnproven
    , ProofState (..)
    , proofState
    , ProofStateTransformer (..)
    ) where

import Data.Hashable
import GHC.Generics as GHC

{- | The state of the all-path reachability proof strategy for @goal@.
 -}
data ProofState goal
    = Goal goal
    -- ^ The indicated goal is being proven.
    | GoalRem goal
    -- ^ The indicated goal remains after rewriting.
    | Proven
    -- ^ The parent goal was proven.
    deriving (Eq, Show, Ord, Functor, Generic)

instance Hashable goal => Hashable (ProofState goal)

{- | Extract the unproven goals of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ProofState goal -> Maybe goal
extractUnproven (Goal t)    = Just t
extractUnproven (GoalRem t) = Just t
extractUnproven Proven      = Nothing

extractGoalRem :: ProofState goal -> Maybe goal
extractGoalRem (GoalRem t) = Just t
extractGoalRem _           = Nothing

data ProofStateTransformer goal a =
    ProofStateTransformer
        { goalTransformer :: goal -> a
        , goalRemTransformer :: goal -> a
        , provenValue :: a
        }

{- | Catamorphism for 'ProofState'
-}
proofState
    :: ProofStateTransformer goal a
    -> ProofState goal
    -> a
proofState
    ProofStateTransformer
        {goalTransformer, goalRemTransformer, provenValue}
  =
    \case
        Goal goal -> goalTransformer goal
        GoalRem goal -> goalRemTransformer goal
        Proven -> provenValue
