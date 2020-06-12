module Kore.Log.DebugUnificationUnified
    ( DebugUnificationUnified (..)
    , debugUnificationUnified
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
    )
import qualified Pretty

data DebugUnificationUnified =
    DebugUnificationUnified
    { evaluator :: Text
    , term1 :: TermLike VariableName
    , term2 :: TermLike VariableName
    , result :: Pattern VariableName
    }
    deriving Show

instance Pretty DebugUnificationUnified where
    pretty DebugUnificationUnified { evaluator, term1, term2, result } =
        Pretty.vsep
        [ Pretty.hsep
            [ "Evaluator", Pretty.pretty evaluator, "applied to:" ]
        , Pretty.indent 4 (unparse term1)
        , "and:"
        , Pretty.indent 4 (unparse term2)
        , "result:"
        , Pretty.indent 4 (unparse result)
        ]

instance Entry DebugUnificationUnified where
    entrySeverity _ = Debug

debugUnificationUnified
    :: MonadLog m
    => InternalVariable variable
    => Text
    -> TermLike variable
    -> TermLike variable
    -> Pattern variable
    -> m ()
debugUnificationUnified evaluator term1' term2' result' =
    logEntry DebugUnificationUnified { evaluator, term1, term2, result }
  where
    term1 = TermLike.mapVariables (pure toVariableName) term1'
    term2 = TermLike.mapVariables (pure toVariableName) term2'
    result = Pattern.mapVariables (pure toVariableName) result'
