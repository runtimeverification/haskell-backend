{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
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

import Control.Monad.Extra as Monad
import qualified Data.Char as Char
import Data.Limit (
    Limit (..),
    maybeLimit,
 )
import Data.List (
    intercalate,
 )
import Kore.Parser.ParserUtils (
    readPositiveIntegral,
 )
import Options.Applicative (
    Parser,
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
import Prelude.Kore
import SMT hiding (
    Solver,
    not,
 )
import System.Directory (
    copyFile,
    doesFileExist,
 )
import System.FilePath (
    (</>),
 )

-- | Command line options for the SMT solver.
data KoreSolverOptions = KoreSolverOptions
    { timeOut :: !TimeOut
    , rLimit :: !RLimit
    , resetInterval :: !ResetInterval
    , prelude :: !Prelude
    , solver :: !Solver
    }

parseKoreSolverOptions :: Parser KoreSolverOptions
parseKoreSolverOptions =
    KoreSolverOptions
        <$> parseTimeOut
        <*> parseRLimit
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

    parseRLimit =
        option
            readRLimit
            ( metavar "SMT_RLIMIT"
                <> long "smt-rlimit"
                <> help "Resource limit for calls to the SMT solver"
                <> value defaultRLimit
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

    SMT.Config
        { timeOut = defaultTimeOut
        , rLimit = defaultRLimit
        , resetInterval = defaultResetInterval
        } =
            SMT.defaultConfig

    readTimeOut = readPositiveIntegral (SMT.TimeOut . Limit) "smt-timeout"
    readRLimit = readPositiveIntegral (SMT.RLimit . Limit) "smt-rlimit"
    readResetInterval =
        readPositiveIntegral SMT.ResetInterval "smt-reset-interval"

unparseKoreSolverOptions :: KoreSolverOptions -> [String]
unparseKoreSolverOptions
    KoreSolverOptions
        { timeOut = TimeOut unwrappedTimeOut
        , rLimit = RLimit unwrappedRLimit
        , resetInterval
        , prelude = Prelude unwrappedPrelude
        , solver
        } =
        catMaybes
            [ (\limit -> unwords ["--smt-timeout", show limit])
                <$> maybeLimit Nothing Just unwrappedTimeOut
            , (\limit -> unwords ["--smt-rlimit", show limit])
                <$> maybeLimit Nothing Just unwrappedRLimit
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
    deriving stock (Eq, Ord, Show)
    deriving stock (Enum, Bounded)

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
