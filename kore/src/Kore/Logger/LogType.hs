{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Logger.LogType
    ( KoreLogType (..)
    , parseCommandLine
    ) where

import Options.Applicative
    ( Parser
    , help
    , long
    , maybeReader
    , option
    )

-- | 'KoreLogType' is passed via command line arguments and decides if and how
-- the logger will operate.
data KoreLogType
    = LogNone
    -- ^ No logging
    | LogStdErr
    -- ^ Log to stderr
    | LogFileText FilePath
    -- ^ Log to specified file when, e.g. when '--log <filename>' is passed.
    deriving (Eq, Show)

parseCommandLine :: String -> Parser KoreLogType
parseCommandLine flagName =
    option
        (maybeReader parseTypeString)
        $ long flagName
        <> help "Name of the log file"

  where
    parseTypeString filename =
        case filename of
            "none" -> pure LogNone
            "stderr" -> pure LogStdErr
            _ -> pure $ LogFileText filename
