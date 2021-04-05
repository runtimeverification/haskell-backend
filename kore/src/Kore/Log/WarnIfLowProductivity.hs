{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.WarnIfLowProductivity (
    WarnIfLowProductivity (..),
    warnIfLowProductivity,
) where

import Log
import Numeric.Natural
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty
import Stats

data WarnIfLowProductivity = WarnIfLowProductivity
    { productivityPercent :: !Natural
    , definitionFileName :: !FilePath
    }
    deriving (Show)

instance Pretty WarnIfLowProductivity where
    pretty warn =
        Pretty.vsep
            [ Pretty.pretty definitionFileName <> Pretty.colon
            , Pretty.hsep
                [ "Productivity dropped to:"
                , Pretty.pretty productivityPercent <> "%"
                ]
            , "Poor productivity may indicate a performance bug."
            , "Please file a bug report: https://github.com/kframework/kore/issues"
            ]
      where
        WarnIfLowProductivity{productivityPercent} = warn
        WarnIfLowProductivity{definitionFileName} = warn

instance Entry WarnIfLowProductivity where
    entrySeverity _ = Warning
    helpDoc _ = "warn when productivty (MUT time / Total time) drops below 90%"

warnIfLowProductivity :: MonadLog log => MonadIO log => FilePath -> log ()
warnIfLowProductivity definitionFileName = do
    Stats{gc_cpu_ns, cpu_ns} <- liftIO getStats
    let gcTimeOver10Percent = gc_cpu_ns * 10 > cpu_ns
        gcPercentage = gc_cpu_ns * 100 `div` cpu_ns
        productivityPercent = 100 - gcPercentage & fromIntegral
        runTimeOver60Seconds = cpu_ns >= 60 * 10 ^ (9 :: Int)
        warn =
            WarnIfLowProductivity
                { productivityPercent
                , definitionFileName
                }
    when (runTimeOver60Seconds && gcTimeOver10Percent) (logEntry warn)
