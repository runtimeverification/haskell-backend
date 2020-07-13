{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.BugReport
    ( BugReport (..)
    , parseBugReport
    , withBugReport
    -- * Re-exports
    , ExitCode (..)
    ) where

import Prelude.Kore

import qualified Codec.Archive.Tar as Tar
import qualified Codec.Compression.GZip as GZip
import Control.Monad.Catch
    ( ExitCase (..)
    , displayException
    , generalBracket
    )
import qualified Data.ByteString.Lazy as ByteString.Lazy
import qualified Data.Foldable as Foldable
import Options.Applicative
import System.Directory
    ( listDirectory
    , removePathForcibly
    )
import System.Exit
    ( ExitCode (..)
    )
import System.FilePath
    ( (<.>)
    , (</>)
    )
import System.IO
    ( hPutStrLn
    , stderr
    )
import System.IO.Temp
    ( createTempDirectory
    , getCanonicalTemporaryDirectory
    )

import Kore.Log.KoreLogOptions
    ( ExeName (..)
    )

newtype BugReport = BugReport { toReport :: Maybe FilePath }
    deriving Show

parseBugReport :: Parser BugReport
parseBugReport =
    BugReport
        <$> optional
            ( strOption
                ( metavar "REPORT_FILE"
                <> long "bug-report"
                <> help "Generate reproducible example of bug at REPORT_FILE.tar.gz"
                )
            )

{- | Create a @.tar.gz@ archive containing the bug report.
 -}
writeBugReportArchive
    :: FilePath   -- ^ Directory to archive
    -> FilePath   -- ^ Name of the archive file, without extension.
    -> IO ()
writeBugReportArchive base tar = do
    contents <- listDirectory base
    let filename = tar <.> "tar" <.> "gz"
    ByteString.Lazy.writeFile filename . GZip.compress . Tar.write
        =<< Tar.pack base contents
    (hPutStrLn stderr . unwords) ["Created bug report:", filename]

{- | Run the inner action with a temporary directory holding the bug report.

The bug report will be saved as an archive if that was requested by the user, or
if there is an error in the inner action.

 -}
withBugReport
    :: ExeName
    -> BugReport
    -> (FilePath -> IO ExitCode)
    -> IO ExitCode
withBugReport exeName bugReport act = do
    (exitCode, _) <-
        generalBracket
            acquireTempDirectory
            releaseTempDirectory
            act
    pure exitCode
  where
    acquireTempDirectory = do
        tmp <- getCanonicalTemporaryDirectory
        createTempDirectory tmp (getExeName exeName)
    releaseTempDirectory tmpDir exitCase = do
        case exitCase of
            ExitCaseSuccess _ -> optionalWriteBugReport tmpDir
            ExitCaseException someException -> do
                let message = displayException someException
                writeFile (tmpDir </> "error" <.> "log") message
                alwaysWriteBugReport tmpDir
            ExitCaseAbort -> alwaysWriteBugReport tmpDir
        removePathForcibly tmpDir
    alwaysWriteBugReport tmpDir =
        writeBugReportArchive tmpDir
            (fromMaybe (getExeName exeName) (toReport bugReport))
    optionalWriteBugReport tmpDir =
        Foldable.traverse_
            (writeBugReportArchive tmpDir)
            (toReport bugReport)
