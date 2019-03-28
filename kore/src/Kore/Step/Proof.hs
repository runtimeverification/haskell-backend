{-|
Module      : Kore.OnePath.Step
Description : Single and multiple step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Proof
    ( StepProof (..)
    , StepProofAtom (..)
    , VariableRenaming (..)
    , stepProof
    , simplificationProof
    , stepProofSumName
    ) where

import qualified Data.Foldable as Foldable
import           Data.Hashable
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq
import           GHC.Generics
                 ( Generic )

import Kore.Step.Simplification.Data
       ( SimplificationProof )
import Kore.Unification.Data
       ( UnificationProof )

{- | 'StepProof' is the proof for an execution step or steps.
 -}
newtype StepProof (level :: *) (variable :: * -> *) =
    StepProof { getStepProof :: Seq (StepProofAtom level variable) }
  deriving (Eq, Show)

instance Hashable (variable level) => Hashable (StepProof level variable) where
    hashWithSalt s = Foldable.foldl' hashWithSalt s . getStepProof

instance Semigroup (StepProof level variable) where
    (<>) (StepProof a) (StepProof b) = StepProof (a <> b)

instance Monoid (StepProof level variable) where
    mempty = StepProof mempty
    mappend = (<>)

stepProof :: StepProofAtom level variable -> StepProof level variable
stepProof atom = StepProof (Seq.singleton atom)

simplificationProof :: SimplificationProof level -> StepProof level variable
simplificationProof = stepProof . StepProofSimplification

{- | The smallest unit of a 'StepProof'.

  @StepProofAtom@ encapsulates the separate proofs resulting from unification,
  variable renaming, and simplification.

 -}
data StepProofAtom (level :: *) (variable :: * -> *)
    = StepProofUnification !(UnificationProof level variable)
    -- ^ Proof for a unification that happened during the step.
    | StepProofVariableRenamings [VariableRenaming level variable]
    -- ^ Proof for the remanings that happened during ther proof.
    | StepProofSimplification !(SimplificationProof level)
    -- ^ Proof for the simplification part of a step.
    deriving (Show, Eq, Generic)

instance Hashable (variable level) => Hashable (StepProofAtom level variable)

{-| 'stepProofSumName' extracts the constructor name for a 'StepProof' -}
stepProofSumName :: StepProofAtom variable level -> String
stepProofSumName (StepProofUnification _)       = "StepProofUnification"
stepProofSumName (StepProofVariableRenamings _) = "StepProofVariableRenamings"
stepProofSumName (StepProofSimplification _)    = "StepProofSimplification"

{-| 'VariableRenaming' represents a renaming of a variable.
-}
data VariableRenaming level variable = VariableRenaming
    { variableRenamingOriginal :: variable level
    , variableRenamingRenamed  :: variable level
    }
    deriving (Eq, Generic, Show)

instance Hashable (variable level) => Hashable (VariableRenaming level variable)
