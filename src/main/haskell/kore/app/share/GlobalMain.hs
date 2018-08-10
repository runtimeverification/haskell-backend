{-# LANGUAGE TemplateHaskell #-}

module GlobalMain
    ( MainOptions(..)
    , GlobalOptions(..)
    , mainGlobal
    , defaultMainGlobal
    , enableDisableFlag
    , clockSomething
    , clockSomethingIO
    ) where

import Control.Exception
       ( evaluate )
import Control.Monad
       ( when )
import Data.Semigroup
       ( mempty, (<>) )
import Data.Time.Format
       ( defaultTimeLocale, formatTime )
import Data.Time.LocalTime
       ( ZonedTime, getZonedTime )
import Data.Version
       ( showVersion )
import System.Clock
       ( Clock (Monotonic), diffTimeSpec, getTime )
import Development.GitRev
       ( gitBranch, gitCommitDate, gitHash )
import Options.Applicative
       ( InfoMod, Parser, argument, disabled, execParser, flag, flag', help,
       helper, hidden, info, internal, long, (<**>), (<|>) )

import qualified Paths_kore as MetaData
                 ( version )

{- | Record Type containing common command-line arguments for each executable in
the project -}
data GlobalOptions = GlobalOptions
    { willVersion    :: !Bool -- ^ Version flag [default=false]
    }


-- | Record type to store all state and options for the subMain operations
data MainOptions a = MainOptions
    { globalOptions :: !GlobalOptions
    , localOptions  :: !(Maybe a)
    }


{- |
Global main function parses command line arguments, handles global flags
and returns the parsed options
-}
mainGlobal
    :: Parser options                -- ^ local options parser
    -> InfoMod (MainOptions options) -- ^ option parser information
    -> IO      (MainOptions options)
mainGlobal localOptionsParser modifiers = do
  options <- commandLineParse localOptionsParser modifiers
  when (willVersion $ globalOptions options) (getZonedTime >>= mainVersion)
  return options


defaultMainGlobal :: IO (MainOptions options)
defaultMainGlobal = mainGlobal (argument disabled mempty) mempty


-- | main function to print version information
mainVersion :: ZonedTime -> IO ()
mainVersion time =
      mapM_ putStrLn
      [ "K framework version " ++ packageVersion
      , "Git:"
      , "  revision:\t"    ++ $gitHash
      , "  branch:\t"      ++ $gitBranch
      , "  last commit:\t" ++  gitTime
      , "Build date:\t"    ++  exeTime
      ]
    where
      packageVersion = showVersion MetaData.version
      formatGit (_:mm:dd:tt:yy:tz:_) = [yy,mm,dd,tt,tz]
      formatGit t                    = t
      gitTime = (unwords . formatGit . words) $gitCommitDate
      exeTime = formatTime defaultTimeLocale  "%Y %b %d %X %z" time


--------------------
-- Option Parsers --

-- | Global Main argument parser for common options
globalCommandLineParser :: Parser GlobalOptions
globalCommandLineParser =
    GlobalOptions
    <$> flag False True
        (  long "version"
        <> help "Print version information" )


-- | Run argument parser for local executable
commandLineParse
    :: Parser a                -- ^ local options parser
    -> InfoMod (MainOptions a) -- ^ local parser info modifiers
    -> IO (MainOptions a)
commandLineParse localCommandLineParser modifiers =
    execParser
    $ info
      ( MainOptions
        <$> globalCommandLineParser
        <*> (   Just <$> localCommandLineParser
            <|> pure Nothing )
      <**> helper )
    modifiers


----------------------
-- Helper Functions --

{-|
Parser builder to create an optional boolean flag,
with an enabled, disabled and default value.
Based on `enableDisableFlagNoDefault`
from commercialhaskell/stack:
https://github.com/commercialhaskell/stack/blob/master/src/Options/Applicative/Builder/Extra.hs
-}
enableDisableFlag
    :: String -- ^ flag name
    -> option -- ^ enabled value
    -> option -- ^ disabled value
    -> option -- ^ default value
    -> String -- ^ Help text suffix; appended to "Enable/disable "
    -> Parser option
enableDisableFlag name enabledVal disabledVal defaultVal helpSuffix =
    flag' enabledVal
        (  hidden
        <> internal
        <> long name
        <> help helpSuffix)
    <|> flag' disabledVal
        (  hidden
        <> internal
        <> long ("no-" ++ name)
        <> help helpSuffix )
    <|> flag' disabledVal
        (  long ( "[no-]" ++ name )
        <> help ( "Enable/disable " ++ helpSuffix ) )
    <|> pure defaultVal


-- | Time a pure computation and print results.
clockSomething :: String -> a -> IO a
clockSomething description something =
    clockSomethingIO description (evaluate something)


-- | Time an IO computation and print results.
clockSomethingIO :: String -> IO a -> IO a
clockSomethingIO description something = do
    start <- getTime Monotonic
    x     <- something
    end   <- getTime Monotonic
    putStrLn $ description ++" "++ show (diffTimeSpec end start)
    return x
