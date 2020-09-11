{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Log.DebugProofState
    ( DebugProofState (..)
    ) where

import Prelude.Kore

import Kore.Step.ClaimPattern
    ( ReachabilityClaim (..)
    )
import Kore.Strategies.ProofState
    ( Prim (..)
    , ProofState (..)
    )
import Log
import Pretty
    ( Pretty (..)
    )
import qualified Pretty

data DebugProofState =
    DebugProofState
        { proofState :: ProofState ReachabilityClaim
        , transition :: Prim
        , result :: Maybe (ProofState ReachabilityClaim)
        }
    deriving (Show)

instance Pretty DebugProofState where
    pretty
        DebugProofState
            { proofState
            , transition
            , result
            }
      =
        Pretty.vsep
            [ "Reached proof state with the following configuration:"
            , Pretty.indent 4 (pretty proofState)
            , "On which the following transition applies:"
            , Pretty.indent 4 (pretty transition)
            , "Resulting in:"
            , Pretty.indent 4 (maybe "Terminal state." pretty result)
            ]

instance Entry DebugProofState where
    entrySeverity _ = Debug
    helpDoc _ = "log proof state"
