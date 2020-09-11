{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Reachability.ClaimState
    ( extractGoalRem
    , extractUnproven
    , extractGoalStuck
    , ClaimState (..)
    , Prim (..)
    , proofState
    , ClaimStateTransformer (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
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
data Prim
    = Begin
    -- ^ The start of each proof step
    | Simplify
    | CheckImplication
    -- ^ Check if the claim's implication is valid.
    | ApplyClaims
    | ApplyAxioms
    deriving (Show)

instance Pretty Prim where
    pretty Begin = "begin proof step"
    pretty Simplify = "simplify the claim"
    pretty CheckImplication = "check implication"
    pretty ApplyClaims = "apply claims"
    pretty ApplyAxioms = "apply axioms"

{- | The state of the reachability proof strategy for @goal@.
 -}
data ClaimState goal
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

instance NFData goal => NFData (ClaimState goal)

instance Hashable goal => Hashable (ClaimState goal)

instance SOP.Generic (ClaimState a)

instance SOP.HasDatatypeInfo (ClaimState a)

instance Debug a => Debug (ClaimState a)

instance (Debug a, Diff a) => Diff (ClaimState a)

instance Unparse goal => Pretty (ClaimState goal) where
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

{- | Extract the unproven goals of a 'ClaimState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ClaimState a -> Maybe a
extractUnproven (Goal t)    = Just t
extractUnproven (GoalRewritten t) = Just t
extractUnproven (GoalRemainder t) = Just t
extractUnproven (GoalStuck t) = Just t
extractUnproven Proven      = Nothing

extractGoalRem :: ClaimState a -> Maybe a
extractGoalRem (GoalRemainder t) = Just t
extractGoalRem _           = Nothing

extractGoalStuck :: ClaimState a -> Maybe a
extractGoalStuck (GoalStuck a) = Just a
extractGoalStuck _             = Nothing

data ClaimStateTransformer a val =
    ClaimStateTransformer
        { goalTransformer :: a -> val
        , goalRemainderTransformer :: a -> val
        , goalRewrittenTransformer :: a -> val
        , goalStuckTransformer :: a -> val
        , provenValue :: val
        }

{- | Catamorphism for 'ClaimState'
-}
proofState
    :: ClaimStateTransformer a val
    -> ClaimState a
    -> val
proofState
    ClaimStateTransformer
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
