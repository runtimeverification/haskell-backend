module Kore.Log.DebugUnificationUnknown
    ( DebugUnificationUnknown (..)
    , debugUnificationUnknown
    ) where

import Prelude.Kore

import Data.Text
    ( Text
    )

import Kore.Internal.TermLike as TermLike
import Kore.Unparser
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data DebugUnificationUnknown =
    DebugUnificationUnknown
    { evaluator :: Text
    , term1 :: TermLike VariableName
    , term2 :: TermLike VariableName
    }
    deriving Show

instance Pretty DebugUnificationUnknown where
    pretty DebugUnificationUnknown { evaluator, term1, term2 } =
        Pretty.vsep
        [ Pretty.hsep
            [ "Evaluator", Pretty.pretty evaluator, "does not apply to:" ]
        , Pretty.indent 4 (unparse term1)
        , "and:"
        , Pretty.indent 4 (unparse term2)
        ]

instance Entry DebugUnificationUnknown where
    entrySeverity _ = Debug

debugUnificationUnknown
    :: MonadLog m
    => InternalVariable variable
    => Text
    -> TermLike variable
    -> TermLike variable
    -> m ()
debugUnificationUnknown evaluator term1' term2' =
    logEntry DebugUnificationUnknown { evaluator, term1, term2 }
  where
    term1 = TermLike.mapVariables (pure toVariableName) term1'
    term2 = TermLike.mapVariables (pure toVariableName) term2'
