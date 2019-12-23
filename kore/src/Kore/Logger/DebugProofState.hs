{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.DebugProofState
    ( debugProofStateBefore
    , debugProofStateAfter
    ) where

import Data.Text
    ( Text
    )
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
        { configuration :: !(ProofState (RulePattern Variable))
        -- , transition :: Prim (RulePattern Variable)
        , transition :: !Text
        , result :: !(Maybe (ProofState (RulePattern Variable)))
        , transitionState :: TransitionState
        }

data TransitionState
    = Before
    | After
    deriving Eq

instance Pretty DebugProofState where
    pretty
        DebugProofState
            { configuration
            , transition
            , result
            , transitionState
            }
      =
        case transitionState of
            Before ->
                Pretty.vsep
                    [ "Reached proof state with the following configuration:"
                    , Pretty.indent 4 (pretty configuration)
                    ]
            After ->
                Pretty.vsep
                    [ "On which the following transition applies:"
                    , Pretty.indent 4 (pretty transition)
                    , "Resulting in:"
                    , Pretty.indent 4 (pretty result)
                    ]

instance Entry DebugProofState where
    entrySeverity _ = Debug

debugProofStateBefore
    :: MonadLog log
    => ProofState (RulePattern Variable)
    -> Text
    -> Maybe (ProofState (RulePattern Variable))
    -> log ()
debugProofStateBefore =
    logTransitionState Before

debugProofStateAfter
    :: MonadLog log
    => ProofState (RulePattern Variable)
    -> Text
    -> Maybe (ProofState (RulePattern Variable))
    -> log ()
debugProofStateAfter =
    logTransitionState After

logTransitionState
    :: MonadLog log
    => TransitionState
    -> ProofState (RulePattern Variable)
    -> Text
    -> Maybe (ProofState (RulePattern Variable))
    -> log ()
logTransitionState
    transitionState
    configuration
    transition
    result
  =
    logM DebugProofState
        { configuration
        , transition
        , result
        , transitionState
        }
