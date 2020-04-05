{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.DebugEvaluateCondition
    ( DebugEvaluateCondition (..)
    , debugEvaluateCondition
    ) where

import Prelude.Kore

import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.Unparser
import Log
import qualified SQL

newtype DebugEvaluateCondition =
    DebugEvaluateCondition { getCondition :: Predicate Variable }
    deriving (GHC.Generic)

instance SOP.Generic DebugEvaluateCondition

instance SOP.HasDatatypeInfo DebugEvaluateCondition

instance Pretty DebugEvaluateCondition where
    pretty = pretty . unparseToString . getCondition

instance Entry DebugEvaluateCondition where
    entrySeverity _ = Debug

instance SQL.Table DebugEvaluateCondition

debugEvaluateCondition
    :: MonadLog log
    => InternalVariable variable
    => Predicate variable -> log ()
debugEvaluateCondition predicate =
    logEntry
    $ DebugEvaluateCondition
    $ Predicate.externalizeFreshVariables predicate
