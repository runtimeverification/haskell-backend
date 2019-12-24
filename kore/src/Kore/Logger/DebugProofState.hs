{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.DebugProofState
    ( debugProofState
    , debugProofStateBefore
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
        { configuration :: !(Maybe (ProofState (RulePattern Variable)))
        , transition :: !(Maybe (Prim (RulePattern Variable)))
        , result :: !(Maybe (ProofState (RulePattern Variable)))
        , transitionState :: TransitionState
        }

data TransitionState
    = Before
    | After
    | Both
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
            Before -> beforeText
            After  -> afterText
            Both   -> beforeText <> afterText
      where
        beforeText =
            Pretty.vsep
                [ "Reached proof state with the following configuration:"
                , Pretty.indent 4 (pretty configuration)
                ]
        afterText =
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
    => Maybe (ProofState (RulePattern Variable))
    -> log ()
debugProofStateBefore config =
    logTransitionState Both config Nothing Nothing

debugProofStateAfter
    :: MonadLog log
    => Maybe (Prim (RulePattern Variable))
    -> Maybe (ProofState (RulePattern Variable))
    -> log ()
debugProofStateAfter =
    logTransitionState After Nothing

debugProofState
    :: MonadLog log
    => Maybe (ProofState (RulePattern Varable))
    -> Maybe (Prim (RulePattern Variable))
    -> Maybe (ProofState (RulePattern Variable))
    -> log ()
debugProofState =
    logTransitionState Both

logTransitionState
    :: MonadLog log
    => TransitionState
    -> Maybe (ProofState (RulePattern Varable))
    -> Maybe (Prim (RulePattern Variable))
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
