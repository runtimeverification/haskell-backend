{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Options.SMT
    ( KoreSolverOptions (..)
    , Prelude (..)
    , Solver (..)
    , parseKoreSolverOptions
    , unparseKoreLogOptions
    ) where

import Prelude.Kore

import qualified Data.Char as Char
import Data.List
    ( intercalate
    )
import Options.Applicative
    ( InfoMod
    , Parser
    , argument
    , auto
    , fullDesc
    , header
    , help
    , long
    , metavar
    , option
    , progDesc
    , readerError
    , str
    , strOption
    , value
    )
import qualified Options.Applicative as Options

import Data.Limit
    ( Limit (..)
    , maybeLimit
    )
import SMT hiding
    ( Solver
    )

data KoreSolverOptions = KoreSolverOptions
    { timeOut :: !TimeOut
    , resetInterval :: !ResetInterval
    , prelude :: !Prelude
    , solver :: !Solver
    }

newtype Prelude = Prelude { getPrelude :: Maybe FilePath }

parseKoreSolverOptions :: Parser KoreSolverOptions
parseKoreSolverOptions =
    KoreSolverOptions
    <$> option readSMTTimeOut
        ( metavar "SMT_TIMEOUT"
        <> long "smt-timeout"
        <> help "Timeout for calls to the SMT solver, in milliseconds"
        <> value defaultTimeOut
        )
    <*> option readSMTResetInterval
        ( metavar "SMT_RESET_INTERVAL"
        <> long "smt-reset-interval"
        <> help "Reset the solver after this number of queries"
        <> value defaultResetInterval
        )
    <*>
        (Prelude <$>
            optional
            ( strOption
                ( metavar "SMT_PRELUDE"
                <> long "smt-prelude"
                <> help "Path to the SMT prelude file"
                )
            )
        )
    <*> parseSolver
  where
    SMT.Config { timeOut = defaultTimeOut } = SMT.defaultConfig
    SMT.Config { resetInterval = defaultResetInterval } = SMT.defaultConfig

    readPositiveInteger ctor optionName = do
        readInt <- auto
        when (readInt <= 0) err
        return . ctor $ readInt
      where
        err =
            readerError
            . unwords
            $ [optionName, "must be a positive integer."]

    readSMTTimeOut = readPositiveInteger (SMT.TimeOut . Limit) "smt-timeout"
    readSMTResetInterval =
        readPositiveInteger SMT.ResetInterval "smt-reset-interval"

unparseKoreLogOptions = undefined

-- | Available SMT solvers
data Solver = Z3 | None
    deriving (Eq, Ord, Show)
    deriving (Enum, Bounded)

parseSolver :: Parser Solver
parseSolver =
    option (snd <$> readSum longName options)
    $  metavar "SOLVER"
    <> long longName
    <> help ("SMT solver for checking constraints: " <> knownOptions)
    <> value Z3
  where
    longName = "smt"
    knownOptions = intercalate ", " (map fst options)
    options = [ (map Char.toLower $ show s, s) | s <- [minBound .. maxBound] ]

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
