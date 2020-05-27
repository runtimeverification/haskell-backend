{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.BugReport
    ( BugReport (..)
    , parseBugReport
    ) where

import Prelude.Kore

import Options.Applicative

newtype BugReport = BugReport { toReport :: Maybe FilePath }
    deriving Show

parseBugReport :: Parser BugReport
parseBugReport =
    BugReport
        <$> optional
            ( strOption
                ( metavar "REPRT FILE"
                <> long "bug-report"
                <> help "Whether to report a bug"
                )
            )
