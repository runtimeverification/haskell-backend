{-# LANGUAGE TemplateHaskell #-}

module GlobalMain
    ( MainOptions(..)
    , GlobalOptions(..)
    , KoreProveOptions(..)
    , KoreMergeOptions(..)
    , Main
    , parseKoreProveOptions
    , parseKoreMergeOptions
    , mainGlobal
    , defaultMainGlobal
    , enableDisableFlag
    , clockSomething
    , clockSomethingIO
    , mainPatternVerify
    , parseDefinition
    , verifyDefinitionWithBase
    , mainParse
    , lookupMainModule
    , LoadedDefinition
    , LoadedModule
    , loadDefinitions
    , loadModule
    ) where

import Colog
    ( (<&)
    )
import Control.Exception
    ( evaluate
    )
import Control.Monad
    ( when
    )
import qualified Control.Monad as Monad
import Control.Monad.Trans.Class
    ( lift
    )
import Data.Function
    ( (&)
    )
import Data.List
    ( intercalate
    )
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import Data.Proxy
    ( Proxy (..)
    )
import Data.Semigroup
    ( (<>)
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    , pack
    )
import Data.Time.Format
    ( defaultTimeLocale
    , formatTime
    )
import Data.Time.LocalTime
    ( ZonedTime
    , getZonedTime
    )
import Data.Version
    ( showVersion
    )
import Development.GitRev
    ( gitBranch
    , gitCommitDate
    , gitHash
    )
import GHC.Stack
    ( emptyCallStack
    )
import Options.Applicative
    ( InfoMod
    , Parser
    , argument
    , disabled
    , execParser
    , flag
    , flag'
    , help
    , helper
    , hidden
    , info
    , internal
    , long
    , metavar
    , option
    , readerError
    , str
    , strOption
    , switch
    , value
    , (<**>)
    , (<|>)
    )
import System.Clock
    ( Clock (Monotonic)
    , diffTimeSpec
    , getTime
    )

import Kore.ASTVerifier.DefinitionVerifier
    ( AttributesVerification (DoNotVerifyAttributes)
    , defaultAttributesVerification
    , verifyAndIndexDefinitionWithBase
    )
import Kore.ASTVerifier.PatternVerifier as PatternVerifier
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.Logger.Output as Logger
import Kore.Parser
    ( ParsedPattern
    , parseKoreDefinition
    )
import Kore.Step.Strategy
    ( GraphSearchOrder (..)
    )
import Kore.Syntax
import Kore.Syntax.Definition
    ( ModuleName (..)
    , ParsedDefinition
    , getModuleNameForError
    )
import qualified Kore.Verified as Verified
import qualified Paths_kore as MetaData
    ( version
    )

type Main = LoggerT IO

data KoreProveOptions =
    KoreProveOptions
        { specFileName :: !FilePath
        -- ^ Name of file containing the spec to be proven
        , specMainModule :: !ModuleName
        -- ^ The main module of the spec to be proven
        , graphSearch :: GraphSearchOrder
        -- ^ Search order of the execution graph
        , bmc :: !Bool
        -- ^ Whether to use bounded model checker
        }

parseKoreProveOptions :: Parser KoreProveOptions
parseKoreProveOptions =
    KoreProveOptions
    <$> strOption
        (  metavar "SPEC_FILE"
        <> long "prove"
        <> help "Kore source file representing spec to be proven.\
                \Needs --spec-module."
        )
    <*> (ModuleName
        <$> strOption
            (  metavar "SPEC_MODULE"
            <> long "spec-module"
            <> help "The name of the main module in the spec to be proven."
            )
        )
    <*> parseGraphSearch
    <*> switch
        ( long "bmc"
        <> help "Whether to use the bounded model checker." )
  where
    parseGraphSearch =
        option readGraphSearch
            (  metavar "GRAPH_SEARCH"
            <> long "graph-search"
            <> value BreadthFirst
            <> help "Search order of the execution graph. \
                    \Either breadth-first or depth-first. \
                    \Default is breadth-first."
            )
      where
        searchOrders =
            [ ("breadth-first", BreadthFirst)
            , ("depth-first", DepthFirst)
            ]
        readGraphSearch = do
            input <- str
            let found = lookup input searchOrders
            case found of
                Just searchOrder -> pure searchOrder
                Nothing ->
                    let
                        unknown = "Unknown search order '" ++ input ++ "'. "
                        names = intercalate ", " (fst <$> searchOrders)
                        known = "Known search order are: " ++ names
                    in
                        readerError (unknown ++ known)

data KoreMergeOptions =
    KoreMergeOptions
        { rulesFileName     :: !FilePath
        -- ^ Name for file containing a sequence of rules to merge.
        }

parseKoreMergeOptions :: Parser KoreMergeOptions
parseKoreMergeOptions =
    KoreMergeOptions
    <$> strOption
            (  metavar "MERGE_RULES_FILE"
            <> long "merge-rules"
            <> help
                "List of rules to merge."
            )

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
                <|> pure Nothing
                )
        <**> helper
        )
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
clockSomething :: String -> a -> Main a
clockSomething description something =
    clockSomethingIO description (evaluate something)


-- | Time an IO computation and print results.
clockSomethingIO :: String -> IO a -> Main a
clockSomethingIO description something = do
    start  <- lift $ getTime Monotonic
    x      <- lift   something
    end    <- lift $ getTime Monotonic
    logger <- askLogAction
    logger <& logMessage end start
    return x
  where
    logMessage end start =
        Logger.LogMessage
            { message =
                pack $ description ++" "++ show (diffTimeSpec end start)
            , severity = Logger.Info
            , scope = [Scope "TimingInfo"]
            , callstack = emptyCallStack
            }

-- | Verify that a Kore pattern is well-formed and print timing information.
mainPatternVerify
    :: VerifiedModule Attribute.Symbol axiomAttrs
    -- ^ Module containing definitions visible in the pattern
    -> ParsedPattern -- ^ Parsed pattern to check well-formedness
    -> Main Verified.Pattern
mainPatternVerify verifiedModule patt = do
    verifyResult <-
        clockSomething "Verifying the pattern"
            (runPatternVerifier context $ verifyStandalonePattern Nothing patt)
    either (error . printError) return verifyResult
  where
    Builtin.Verifiers { domainValueVerifiers } = Builtin.koreVerifiers
    context =
        PatternVerifier.Context
            { indexedModule =
                verifiedModule
                & IndexedModule.eraseAxiomAttributes
            , declaredSortVariables = Set.empty
            , declaredVariables = emptyDeclaredVariables
            , builtinDomainValueVerifiers = domainValueVerifiers
            }

lookupMainModule
    :: Monad monad
    => ModuleName
    -> Map.Map
        ModuleName
        (VerifiedModule Attribute.Symbol Attribute.Axiom)
    -> monad (VerifiedModule Attribute.Symbol Attribute.Axiom)
lookupMainModule name modules =
    case Map.lookup name modules of
        Nothing ->
            error
                (  "The main module, '"
                ++ getModuleNameForError name
                ++ "', was not found. Check the --module flag."
                )
        Just m -> return m

{- | Verify the well-formedness of a Kore definition.

Also prints timing information; see 'mainParse'.

 -}
verifyDefinitionWithBase
    ::  ( Map.Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom)
        , Map.Map Text AstLocation
        )
    -- ^ already verified definition
    -> Bool
    -- ^ whether to check (True) or ignore attributes during verification
    -> ParsedDefinition
    -- ^ Parsed definition to check well-formedness
    -> Main
        ( Map.Map ModuleName
            (VerifiedModule Attribute.Symbol Attribute.Axiom)
        , Map.Map Text AstLocation
        )
verifyDefinitionWithBase
    alreadyVerified
    willChkAttr
    definition
  =
    let attributesVerification =
            if willChkAttr
            then defaultAttributesVerification Proxy Proxy
            else DoNotVerifyAttributes
    in do
      verifyResult <-
        clockSomething "Verifying the definition"
            (verifyAndIndexDefinitionWithBase
                alreadyVerified
                attributesVerification
                Builtin.koreVerifiers
                definition
            )
      case verifyResult of
        Left err1               -> error (printError err1)
        Right indexedDefinition -> return indexedDefinition

{- | Parse a Kore definition from a filename.

Also prints timing information; see 'mainParse'.

 -}
parseDefinition :: FilePath -> Main ParsedDefinition
parseDefinition = mainParse parseKoreDefinition

mainParse
    :: (FilePath -> String -> Either String a)
    -> String
    -> Main a
mainParse parser fileName = do
    contents <-
        clockSomethingIO "Reading the input file" (readFile fileName)
    parseResult <-
        clockSomething "Parsing the file" (parser fileName contents)
    case parseResult of
        Left err         -> error err
        Right definition -> return definition

type LoadedModule = VerifiedModule Attribute.Symbol Attribute.Axiom

type LoadedDefinition = (Map ModuleName LoadedModule, Map Text AstLocation)

loadDefinitions :: [FilePath] -> Main LoadedDefinition
loadDefinitions filePaths =
    Monad.foldM (\loaded -> verifyDefinitionWithBase loaded True) mempty
    =<< traverse parseDefinition filePaths

loadModule :: ModuleName -> LoadedDefinition -> Main LoadedModule
loadModule moduleName = lookupMainModule moduleName . fst
