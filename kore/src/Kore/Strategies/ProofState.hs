{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.ProofState
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
    | GoalRemainder goal
    -- ^ The indicated goal remains after rewriting.
    | GoalRewritten goal
    -- ^ We already rewrote the goal this step.
    | Proven
    -- ^ The parent goal was proven.
    deriving (Eq, Show, Ord, Functor, Generic)

instance Hashable goal => Hashable (ProofState goal)

{- | Extract the unproven goals of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ProofState goal -> Maybe goal
extractUnproven (Goal t)    = Just t
extractUnproven (GoalRewritten t) = Just t
extractUnproven (GoalRemainder t) = Just t
extractUnproven Proven      = Nothing

extractGoalRem :: ProofState goal -> Maybe goal
extractGoalRem (GoalRemainder t) = Just t
extractGoalRem _           = Nothing

data ProofStateTransformer goal a =
    ProofStateTransformer
        { goalTransformer :: goal -> a
        , goalRemainderTransformer :: goal -> a
        , goalRewrittenTransformer :: goal -> a
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
