module Main where

import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.Error
import           Data.Kore.Parser.Parser

import           Control.Exception                        (evaluate)
import           Control.Monad                            (when)
import           System.Clock                             (Clock (Monotonic),
                                                           diffTimeSpec,
                                                           getTime)
import           System.Environment                       (getArgs)

data CommandLineFlags = CommandLineFlags
    { commandLineFlagsFileName :: !(Maybe String)
    , commandLineFlagsVerify   :: !Bool
    , commandLineFlagsPrint    :: !Bool
    }

usage :: String
usage =
    "Usage: kore-parser [--[no]verify] [--[no]print] fileName"

-- TODO(virgil): Use a generic command line parsing library instead.
parseCommandLineFlags :: [String] -> CommandLineFlags
parseCommandLineFlags [] =
    CommandLineFlags
        { commandLineFlagsFileName = Nothing
        , commandLineFlagsVerify = True
        , commandLineFlagsPrint = True
        }
parseCommandLineFlags (('-' : '-' : firstFlag) : commandLineReminder) =
    addFlagAndContinue firstFlag commandLineReminder
  where
    addFlagAndContinue flag commandLine
        | flag == "verify" =
            (parseCommandLineFlags commandLine)
                { commandLineFlagsVerify = True }
        | flag == "noverify" =
            (parseCommandLineFlags commandLine)
                { commandLineFlagsVerify = False }
        | flag == "print" =
            (parseCommandLineFlags commandLine)
                { commandLineFlagsPrint = True }
        | flag == "noprint" =
            (parseCommandLineFlags commandLine)
                { commandLineFlagsPrint = False }
        | otherwise =
            error ("Unknown flag: --" ++ flag)
parseCommandLineFlags (flag : commandLine) =
    (parseCommandLineFlags commandLine) { commandLineFlagsFileName = Just flag }

clockSomething :: String -> a -> IO a
clockSomething description something =
    clockSomethingIO description (evaluate something)

clockSomethingIO :: String -> IO a -> IO a
clockSomethingIO description something = do
    start <- getTime Monotonic
    x <- something
    end <- getTime Monotonic
    print (description ++ show (diffTimeSpec end start))
    return x

main :: IO ()
main = do
    commandLineFlags <- parseCommandLineFlags <$> getArgs

    case commandLineFlagsFileName commandLineFlags of
        Nothing -> do
            print usage
            error "Invalid command line flags."
        Just fileName -> do
            contents <-
                clockSomethingIO "Reading the input file" (readFile fileName)
            parseResult <-
                clockSomething "Parsing the file" (fromKore fileName contents)
            unverifiedDefinition <-
                case parseResult of
                    Left err         -> error err
                    Right definition -> return definition
            verifiedDefinition <-
                if commandLineFlagsVerify commandLineFlags
                    then do
                        verifyResult <-
                            clockSomething
                                "Verifying the definition"
                                (verifyDefinition DoNotVerifyAttributes unverifiedDefinition)
                        case verifyResult of
                            Left err1        -> error (printError err1)
                            Right definition -> return unverifiedDefinition
                    else
                        return unverifiedDefinition
            when
                (commandLineFlagsPrint commandLineFlags)
                (print verifiedDefinition)

