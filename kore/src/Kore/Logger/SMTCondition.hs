{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Logger.SMTCondition
    ( SMTCondition (..)
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

newtype SMTCondition variable =
    SMTCondition
        { getCondition :: Predicate variable 
        }

instance InternalVariable variable => Pretty (SMTCondition variable) where
    pretty SMTCondition { getCondition } =
        pretty $ unparseToString getCondition

instance
    (InternalVariable variable, Typeable variable)
    => Entry (SMTCondition variable)
  where
    entrySeverity _ = Info

logSMTCondition
    :: MonadLog log
    => InternalVariable variable
    => Typeable variable
    => Predicate variable -> log ()
logSMTCondition =
    logM . SMTCondition