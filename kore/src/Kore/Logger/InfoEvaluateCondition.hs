{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Logger.InfoEvaluateCondition
    ( InfoEvaluateCondition (..)
    , logSMTCondition
    ) where

import Kore.Logger
    ( Entry (..)
    , Severity (Info)
    , MonadLog
    , logM
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.TermLike
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import Data.Typeable
import Kore.Unparser

newtype InfoEvaluateCondition =
    InfoEvaluateCondition
        { getCondition :: Predicate Variable 
        }

instance Pretty InfoEvaluateCondition where
    pretty InfoEvaluateCondition { getCondition } =
        pretty $ unparseToString getCondition

instance Entry InfoEvaluateCondition
  where
    entrySeverity _ = Info

infoEvaluateCondition
    :: MonadLog log
    => InternalVariable variable
    => Typeable variable
    => Predicate variable -> log ()
infoEvaluateCondition =
    logM . InfoEvaluateCondition