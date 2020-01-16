{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.InfoEvaluateCondition
    ( InfoEvaluateCondition (..)
    , infoEvaluateCondition
    ) where

import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Internal.Predicate
    ( Predicate
    , freshVariable
    )
import Kore.Internal.TermLike
import Kore.Unparser
import Log
    ( Entry (..)
    , MonadLog
    , Severity (Info)
    , logM
    )
import qualified SQL

newtype InfoEvaluateCondition =
    InfoEvaluateCondition
        { getCondition :: Predicate Variable
        }
    deriving (GHC.Generic)

instance SOP.Generic InfoEvaluateCondition

instance SOP.HasDatatypeInfo InfoEvaluateCondition

instance Pretty InfoEvaluateCondition where
    pretty InfoEvaluateCondition { getCondition } =
        pretty $ unparseToString getCondition

instance Entry InfoEvaluateCondition where
    entrySeverity _ = Info

instance SQL.Table InfoEvaluateCondition where
    createTable = SQL.createTableGeneric
    insertRow = SQL.insertRowGeneric
    selectRow = SQL.selectRowGeneric

infoEvaluateCondition
    :: MonadLog log
    => InternalVariable variable
    => Predicate variable -> log ()
infoEvaluateCondition predicate =
    logM $ InfoEvaluateCondition $ freshVariable predicate
