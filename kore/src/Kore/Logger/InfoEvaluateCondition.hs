{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Logger.InfoEvaluateCondition
    ( InfoEvaluateCondition (..)
    , infoEvaluateCondition
    ) where

import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import Kore.Internal.Predicate
    ( Predicate
    , freshVariable
    )
import Kore.Internal.TermLike
import Kore.Logger
    ( Entry (..)
    , MonadLog
    , Severity (Info)
    , logM
    )
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
    => Predicate variable -> log ()
infoEvaluateCondition predicate =
    logM $ InfoEvaluateCondition $ freshVariable predicate
