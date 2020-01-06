{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.DebugProofState
    ( DebugProofState (..)
    , TransitionState (..)
    ) where

import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Internal.TermLike
    ( Variable
    )
import Kore.Logger
import Kore.Step.RulePattern
    ( ReachabilityRule (..)
    , RewriteRule (..)
    )
import Kore.Strategies.ProofState
    ( Prim (..)
    , ProofState (..)
    )

data DebugProofState =
    DebugProofState
        { configuration :: !TransitionState
        , transition :: !(Prim (RewriteRule Variable))
        }

data TransitionState
    = Before !(ProofState (ReachabilityRule Variable))
    | After  !(ProofState (ReachabilityRule Variable))
    deriving Eq

instance Pretty DebugProofState where
    pretty
        DebugProofState
            { configuration
            , transition
            }
      =
        case configuration of
            Before config ->
                Pretty.vsep
                $ beforeText config <> ["...Applying transition..."]
            After dest ->
                Pretty.vsep (afterText dest)
      where
        beforeText config =
            [ "Reached proof state with the following configuration:"
            , Pretty.indent 4 (pretty config)
            ]
        afterText dest =
            [ "On which the following transition applies:"
            , Pretty.indent 4 (pretty transition)
            , "Resulting in:"
            , Pretty.indent 4 (pretty dest)
            ]

instance Entry DebugProofState where
    entrySeverity _ = Debug
