{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.DebugEvaluateCondition
    ( DebugEvaluateCondition (..)
    , debugEvaluateCondition
    ) where

import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import Kore.Internal.Predicate
    ( Predicate
    , freshVariable
    )
import Kore.Internal.TermLike
import Kore.Unparser
import Log

newtype DebugEvaluateCondition =
    DebugEvaluateCondition { getCondition :: Predicate Variable }

instance Pretty DebugEvaluateCondition where
    pretty = pretty . unparseToString . getCondition

instance Entry DebugEvaluateCondition where
    entrySeverity _ = Debug

debugEvaluateCondition
    :: MonadLog log
    => InternalVariable variable
    => Predicate variable -> log ()
debugEvaluateCondition predicate =
    logM $ DebugEvaluateCondition $ freshVariable predicate
