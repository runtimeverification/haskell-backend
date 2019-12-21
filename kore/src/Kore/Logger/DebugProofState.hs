{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.DebugProofState
    () where

import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Internal.TermLike
    ( Variable
    )
import Kore.Logger
import Kore.Step.Rule
    ( RulePattern (..)
    )
import Kore.Strategies.ProofState
    ( Prim (..)
    , ProofState (..)
    )

data DebugProofState =
    DebugProofState
        { configuration :: ProofState (RulePattern Variable)
        , transition :: Prim (RulePattern Variable)
        , result :: ProofState (RulePattern Variable)
        }

instance Pretty DebugProofState where
    pretty
        DebugProofState
            { configuration, transition, result }
      =
        Pretty.vsep
            [ "Reached proof state with the following configuration:"
            , Pretty.indent 4 (pretty configuration)
            , "On which the following transition applies:"
            , Pretty.indent 4 (pretty transition)
            , "Resulting in:"
            , Pretty.indent 4 (pretty result)
            ]

instance Entry DebugProofState where
    entrySeverity _ = Debug
