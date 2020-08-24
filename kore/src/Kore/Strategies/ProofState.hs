{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.ProofState
    ( extractGoalRem
    , extractUnproven
    , extractGoalStuck
    , ProofState (..)
    , Prim (..)
    , proofState
    , ProofStateTransformer (..)
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

instance NFData goal => NFData (ProofState goal)

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

extractGoalStuck :: ProofState a -> Maybe a
extractGoalStuck (GoalStuck a) = Just a
extractGoalStuck _             = Nothing

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
