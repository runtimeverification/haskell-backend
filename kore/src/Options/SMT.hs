{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Options.SMT (
    KoreSolverOptions (..),
    Solver (..),
    parseKoreSolverOptions,
    unparseKoreSolverOptions,
    defaultSmtPreludeFilePath,
    writeKoreSolverFiles,
    ensureSmtPreludeExists,
) where

import Prelude.Kore

import Control.Monad.Extra as Monad
import qualified Data.Char as Char
import Data.List (
    intercalate,
 )
import Options.Applicative (
    Parser,
    auto,
    help,
    long,
    metavar,
    option,
    readerError,
    str,
    strOption,
    value,
 )
import qualified Options.Applicative as Options
import System.Directory (
    copyFile,
    doesFileExist,
 )
import System.FilePath (
    (</>),
 )

import Data.Limit (
    Limit (..),
    maybeLimit,
 )
import SMT hiding (
    Solver,
    not,
 )

-- | Command line options for the SMT solver.
data KoreSolverOptions = KoreSolverOptions
    { timeOut :: !TimeOut
    , resetInterval :: !ResetInterval
    , prelude :: !Prelude
    , solver :: !Solver
    }

parseKoreSolverOptions :: Parser KoreSolverOptions
parseKoreSolverOptions =
    KoreSolverOptions
        <$> parseTimeOut
        <*> parseResetInterval
        <*> parsePrelude
        <*> parseSolver
  where
    parseTimeOut =
        option
            readTimeOut
            ( metavar "SMT_TIMEOUT"
                <> long "smt-timeout"
                <> help "Timeout for calls to the SMT solver, in milliseconds"
                <> value defaultTimeOut
            )

    parseResetInterval =
        option
            readResetInterval
            ( metavar "SMT_RESET_INTERVAL"
                <> long "smt-reset-interval"
                <> help "Reset the solver after this number of queries"
                <> value defaultResetInterval
            )

    parsePrelude =
        Prelude
            <$> optional
                ( strOption
                    ( metavar "SMT_PRELUDE"
                        <> long "smt-prelude"
                        <> help "Path to the SMT prelude file"
                    )
                )

    SMT.Config{timeOut = defaultTimeOut} = SMT.defaultConfig
    SMT.Config{resetInterval = defaultResetInterval} = SMT.defaultConfig

    readPositiveInteger ctor optionName = do
        readInt <- auto
        when (readInt <= 0) err
        return . ctor $ readInt
      where
        err =
            readerError
                . unwords
                $ [optionName, "must be a positive integer."]

    readTimeOut = readPositiveInteger (SMT.TimeOut . Limit) "smt-timeout"
    readResetInterval =
        readPositiveInteger SMT.ResetInterval "smt-reset-interval"

unparseKoreSolverOptions :: KoreSolverOptions -> [String]
unparseKoreSolverOptions
    KoreSolverOptions
        { timeOut = TimeOut unwrappedTimeOut
        , resetInterval
        , prelude = Prelude unwrappedPrelude
        , solver
        } =
        catMaybes
            [ (\limit -> unwords ["--smt-timeout", show limit])
                <$> maybeLimit Nothing Just unwrappedTimeOut
            , pure $
                unwords
                    [ "--smt-reset-interval"
                    , show . getResetInterval $ resetInterval
                    ]
            , unwrappedPrelude
                $> unwords ["--smt-prelude", defaultSmtPreludeFilePath]
            , pure $ unwords ["--smt", unparseSolver solver]
            ]

-- | Available SMT solvers.
data Solver = Z3 | None
    deriving (Eq, Ord, Show)
    deriving (Enum, Bounded)

parseSolver :: Parser Solver
parseSolver =
    option (snd <$> readSum longName options) $
        metavar "SOLVER"
            <> long longName
            <> help ("SMT solver for checking constraints: " <> knownOptions)
            <> value Z3
  where
    longName = "smt"
    knownOptions = intercalate ", " (map fst options)
    options = [(map Char.toLower $ show s, s) | s <- [minBound .. maxBound]]

unparseSolver :: Solver -> String
unparseSolver Z3 = "z3"
unparseSolver None = "none"

readSum :: String -> [(String, value)] -> Options.ReadM (String, value)
readSum longName options = do
    opt <- str
    case lookup opt options of
        Just val -> pure (opt, val)
        _ -> readerError (unknown opt ++ known)
  where
    knownOptions = intercalate ", " (map fst options)
    unknown opt = "Unknown " ++ longName ++ " '" ++ opt ++ "'. "
    known = "Known " ++ longName ++ "s are: " ++ knownOptions ++ "."

defaultSmtPreludeFilePath :: FilePath
defaultSmtPreludeFilePath = "prelude.smt2"

writeKoreSolverFiles :: KoreSolverOptions -> FilePath -> IO ()
writeKoreSolverFiles
    KoreSolverOptions{prelude = Prelude unwrappedPrelude}
    reportFile =
        for_ unwrappedPrelude $
            flip copyFile (reportFile </> defaultSmtPreludeFilePath)

-- | Ensure that the SMT prelude file exists, if specified.
ensureSmtPreludeExists :: KoreSolverOptions -> IO ()
ensureSmtPreludeExists
    KoreSolverOptions
        { prelude = SMT.Prelude unwrappedPrelude
        } =
        traverse_
            ( \filePath ->
                Monad.whenM
                    (not <$> doesFileExist filePath)
                    (error $ "SMT prelude file does not exist: " <> filePath)
            )
            unwrappedPrelude
