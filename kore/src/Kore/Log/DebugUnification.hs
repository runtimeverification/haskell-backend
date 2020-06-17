{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.DebugUnification
    ( DebugUnification (..)
    , debugUnificationResult
    , debugUnificationUnknown
    , whileDebugUnification
    ) where

import Prelude.Kore

import Data.Text
    ( Text
    )

import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike as TermLike
import Kore.Unparser
import Log
import Pretty
    ( Pretty
    , (<+>)
    )
import qualified Pretty

data DebugUnification
    = DebugUnificationWhile !WhileDebugUnification
    | DebugUnificationResult !UnificationResult
    | DebugUnificationUnknown
    deriving Show

instance Pretty DebugUnification where
    pretty (DebugUnificationWhile dbg) = Pretty.pretty dbg
    pretty (DebugUnificationResult dbg) = Pretty.pretty dbg
    pretty DebugUnificationUnknown = "Unknown unification problem"

instance Entry DebugUnification where
    entrySeverity _ = Debug

data WhileDebugUnification =
    WhileDebugUnification
    { term1, term2 :: TermLike VariableName }
    deriving Show

instance Pretty WhileDebugUnification where
    pretty WhileDebugUnification { term1, term2 } =
        Pretty.vsep
        [ "Unifying terms:"
        , Pretty.indent 4 (unparse term1)
        , Pretty.indent 2 "and:"
        , Pretty.indent 4 (unparse term2)
        ]

data UnificationResult =
    UnificationResult
    { evaluator :: Text
    , result :: Pattern VariableName
    }
    deriving Show

instance Pretty UnificationResult where
    pretty UnificationResult { evaluator, result } =
        Pretty.vsep
        [ "Unified by" <+> Pretty.pretty evaluator <> Pretty.colon
        , Pretty.indent 4 (unparse result)
        ]

whileDebugUnification
    :: MonadLog m
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> m a
    -> m a
whileDebugUnification term1' term2' =
    logWhile $ DebugUnificationWhile WhileDebugUnification { term1, term2 }
  where
    term1 = TermLike.mapVariables (pure toVariableName) term1'
    term2 = TermLike.mapVariables (pure toVariableName) term2'

debugUnificationResult
    :: MonadLog m
    => InternalVariable variable
    => Text
    -> Pattern variable
    -> m ()
debugUnificationResult evaluator result' =
    logEntry $ DebugUnificationResult UnificationResult { evaluator, result }
  where
    result = Pattern.mapVariables (pure toVariableName) result'

debugUnificationUnknown :: MonadLog m => m ()
debugUnificationUnknown = logEntry DebugUnificationUnknown
