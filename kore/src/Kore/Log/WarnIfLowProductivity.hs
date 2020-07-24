{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.WarnIfLowProductivity
    ( WarnIfLowProductivity (..)
    , warnIfLowProductivity
    )where

import Prelude.Kore

import Log
import Numeric.Natural
import Pretty
    ( Pretty
    )
import qualified Pretty
import Stats

newtype WarnIfLowProductivity =
    WarnIfLowProductivity { productivityPercent :: Natural }
    deriving Show

instance Pretty WarnIfLowProductivity where
    pretty (WarnIfLowProductivity productivityPercent) =
        Pretty.hsep
            [ "Warning! Poor performance: productivity dropped to aprox."
            , Pretty.pretty productivityPercent <> "%"
            ]

instance Entry WarnIfLowProductivity where
    entrySeverity _ = Warning
    helpDoc _ = "warn when productivty (MUT time / Total time) drops below 90%"

warnIfLowProductivity :: MonadLog log => MonadIO log => log ()
warnIfLowProductivity = do
    Stats { gc_cpu_ns, cpu_ns } <- liftIO getStats
    when (gc_cpu_ns * 10 > cpu_ns) $
        (logEntry . WarnIfLowProductivity)
                (fromIntegral (100 - gc_cpu_ns * 100 `div` cpu_ns))
