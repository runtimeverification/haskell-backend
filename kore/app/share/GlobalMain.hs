{-# LANGUAGE TemplateHaskell #-}

module GlobalMain
    ( MainOptions(..)
    , GlobalOptions(..)
    , KoreProveOptions(..)
    , parseKoreProveOptions
    , mainGlobal
    , defaultMainGlobal
    , enableDisableFlag
    , clockSomething
    , clockSomethingIO
    , mainPatternVerify
    , parseDefinition
    , verifyDefinitionWithBase
    , constructorFunctions
    , mainModule
    , mainParse
    ) where

import           Control.Exception
                 ( evaluate )
import qualified Control.Lens as Lens
import           Control.Monad
                 ( when )
import           Data.Function
                 ( (&) )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Semigroup
                 ( (<>) )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import           Data.Time.Format
                 ( defaultTimeLocale, formatTime )
import           Data.Time.LocalTime
                 ( ZonedTime, getZonedTime )
import           Data.Version
                 ( showVersion )
import           Development.GitRev
                 ( gitBranch, gitCommitDate, gitHash )
import           Options.Applicative
                 ( InfoMod, Parser, argument, disabled, execParser, flag,
                 flag', help, helper, hidden, info, internal, long, metavar,
                 strOption, (<**>), (<|>) )
import           System.Clock
                 ( Clock (Monotonic), diffTimeSpec, getTime )
import           System.IO
                 ( hPutStrLn, stderr )

import           Kore.AST.Kore
import           Kore.AST.Sentence
                 ( KoreDefinition, ModuleName (..), getModuleNameForError )
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (DoNotVerifyAttributes),
                 defaultAttributesVerification,
                 verifyAndIndexDefinitionWithBase )
import           Kore.ASTVerifier.PatternVerifier as PatternVerifier
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), VerifiedModule,
                 makeIndexedModuleAttributesNull, mapIndexedModulePatterns )
import           Kore.Parser.Parser
                 ( parseKoreDefinition )
import           Kore.Step.StepperAttributes
import qualified Paths_kore as MetaData
                 ( version )

data KoreProveOptions =
    KoreProveOptions
        { specFileName :: !FilePath
        -- ^ Name of file containing the spec to be proven
        , specMainModule :: !ModuleName
        -- ^ The main module of the spec to be proven
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
    hPutStrLn stderr $ description ++" "++ show (diffTimeSpec end start)
    return x

-- | Verify that a Kore pattern is well-formed and print timing information.
mainPatternVerify
    :: VerifiedModule declAttrs axiomAttrs
    -- ^ Module containing definitions visible in the pattern
    -> CommonKorePattern -- ^ Parsed pattern to check well-formedness
    -> IO VerifiedKorePattern
mainPatternVerify verifiedModule patt = do
    verifyResult <-
        clockSomething "Verifying the pattern"
            (runPatternVerifier context $ verifyStandalonePattern Nothing patt)
    either (error . printError) return verifyResult
  where
    Builtin.Verifiers { domainValueVerifiers } = Builtin.koreVerifiers
    indexedModule =
        mapIndexedModulePatterns eraseAnnotations verifiedModule
    context =
        PatternVerifier.Context
            { indexedModule = makeIndexedModuleAttributesNull indexedModule
            , declaredSortVariables = Set.empty
            , declaredVariables = emptyDeclaredVariables
            , builtinDomainValueVerifiers = domainValueVerifiers
            }

-- TODO (traiansf): Get rid of this.
-- The function below works around several limitations of
-- the current tool by tricking the tool into believing that
-- functions are constructors (so that function patterns can match)
-- and that @kseq@ and @dotk@ are both functional and constructor.
constructorFunctions
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> VerifiedModule StepperAttributes Attribute.Axiom
constructorFunctions ixm =
    ixm
        { indexedModuleSymbolSentences =
            Map.mapWithKey
                constructorFunctions1
                (indexedModuleSymbolSentences ixm)
        , indexedModuleAliasSentences =
            Map.mapWithKey
                constructorFunctions1
                (indexedModuleAliasSentences ixm)
        , indexedModuleImports = recurseIntoImports <$> indexedModuleImports ixm
        }
  where
    constructorFunctions1 ident (atts, defn) =
        ( atts
            & lensConstructor Lens.<>~ Constructor isCons
            & lensFunctional Lens.<>~ Functional (isCons || isInj)
            & lensInjective Lens.<>~ Injective (isCons || isInj)
            & lensSortInjection Lens.<>~ SortInjection isInj
        , defn
        )
      where
        isInj = getId ident == "inj"
        isCons = elem (getId ident) ["kseq", "dotk"]

    recurseIntoImports (attrs, attributes, importedModule) =
        (attrs, attributes, constructorFunctions importedModule)

mainModule
    :: ModuleName
    -> Map.Map
        ModuleName
        (VerifiedModule StepperAttributes Attribute.Axiom)
    -> IO (VerifiedModule StepperAttributes Attribute.Axiom)
mainModule name modules =
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
    :: Maybe
        ( Map.Map
            ModuleName
            (VerifiedModule StepperAttributes Attribute.Axiom)
        , Map.Map Text AstLocation
        )
    -- ^ base definition to use for verification
    -> Bool -- ^ whether to check (True) or ignore attributes during verification
    -> KoreDefinition -- ^ Parsed definition to check well-formedness
    -> IO
        ( Map.Map
            ModuleName
            (VerifiedModule StepperAttributes Attribute.Axiom)
        , Map.Map Text AstLocation
        )
verifyDefinitionWithBase maybeBaseModule willChkAttr definition =
    let attributesVerification =
            if willChkAttr
            then defaultAttributesVerification Proxy Proxy
            else DoNotVerifyAttributes
    in do
      verifyResult <-
        clockSomething "Verifying the definition"
            (verifyAndIndexDefinitionWithBase
                maybeBaseModule
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
parseDefinition :: FilePath -> IO KoreDefinition
parseDefinition = mainParse parseKoreDefinition

mainParse
    :: (FilePath -> String -> Either String a)
    -> String
    -> IO a
mainParse parser fileName = do
    contents <-
        clockSomethingIO "Reading the input file" (readFile fileName)
    parseResult <-
        clockSomething "Parsing the file" (parser fileName contents)
    case parseResult of
        Left err         -> error err
        Right definition -> return definition
