module Main (main) where

import Control.Monad
    ( when
    )
import Control.Monad.Trans
    ( lift
    )
import Control.Monad.Trans.Reader
    ( runReaderT
    )
import qualified Data.Map as Map
import Data.Proxy
    ( Proxy (..)
    )
import Data.Semigroup
    ( (<>)
    )
import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc.Render.Text
    ( putDoc
    )
import Options.Applicative
    ( InfoMod
    , Parser
    , argument
    , fullDesc
    , header
    , help
    , long
    , metavar
    , progDesc
    , str
    , strOption
    , value
    )

import Kore.AST.ApplicativeKore
import Kore.ASTVerifier.DefinitionVerifier
    ( AttributesVerification (DoNotVerifyAttributes)
    , defaultAttributesVerification
    , verifyAndIndexDefinition
    )
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Symbol
    ( StepperAttributes
    )
import qualified Kore.Builtin as Builtin
import Kore.Debug
import Kore.Error
    ( printError
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    , toVerifiedDefinition
    )
import Kore.Logger.Output
    ( getLoggerT
    )
import qualified Kore.Logger.Output as Logger
import Kore.Parser
    ( ParsedPattern
    , parseKoreDefinition
    , parseKorePattern
    )
import Kore.Syntax.Definition
import Kore.Unparser as Unparser

import GlobalMain

{-
Main module to run kore-parser
TODO: add command line argument tab-completion
-}

-- | Main options record
data KoreParserOptions = KoreParserOptions
    { fileName            :: !FilePath
    -- ^ Name for a file containing a definition to parse and verify
    , patternFileName     :: !FilePath
    -- ^ Name for file containing a pattern to parse and verify
    , mainModuleName      :: !Text
    -- ^ the name of the main module in the definition
    , willPrintDefinition :: !Bool
    -- ^ Option to print definition
    , willPrintPattern    :: !Bool
    -- ^ Option to print pattern
    , willVerify          :: !Bool
    -- ^ Option to verify definition
    , willChkAttr         :: !Bool
    -- ^ Option to check attributes during verification
    , appKore             :: !Bool
    -- ^ Option to print in applicative Kore syntax
    }

-- | Command Line Argument Parser
commandLineParser :: Parser KoreParserOptions
commandLineParser =
    KoreParserOptions
    <$> argument str
        (  metavar "FILE"
        <> help "Kore source file to parse [and verify]" )
    <*> strOption
        (  metavar "PATTERN_FILE"
        <> long "pattern"
        <> help
            "Kore pattern source file to parse [and verify]. Needs --module."
        <> value "" )
    <*> strOption
        (  metavar "MODULE"
        <> long "module"
        <> help "The name of the main module in the Kore definition"
        <> value "" )
    <*> enableDisableFlag "print-definition"
        True False True
        "printing parsed definition to stdout [default enabled]"
    <*> enableDisableFlag "print-pattern"
        True False True
        "printing parsed pattern to stdout [default enabled]"
    <*> enableDisableFlag "verify"
        True False True
        "Verify well-formedness of parsed definition [default enabled]"
    <*> enableDisableFlag "chkattr"
        True False True
        "attributes checking during verification [default enabled]"
    <*> enableDisableFlag "appkore"
        True False False
        (  "printing parsed definition in applicative Kore syntax "
        ++ "[default disabled]"
        )

-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
    <> progDesc "Parses Kore definition in FILE; optionally, \
                \Verifies well-formedness"
    <> header "kore-parser - a parser for Kore definitions"


-- TODO(virgil): Maybe add a regression test for main.
-- | Parses a kore file and Check wellformedness
main :: IO ()
main = do
  options <- mainGlobal commandLineParser parserInfoModifiers
  case localOptions options of
    Nothing ->  -- global options parsed, but local failed; exit gracefully
        return ()
    Just KoreParserOptions
        { fileName
        , patternFileName
        , mainModuleName
        , willPrintDefinition
        , willPrintPattern
        , willVerify
        , willChkAttr
        , appKore
        }
        -> flip runReaderT Logger.emptyLogger . getLoggerT $ do
            parsedDefinition <- mainDefinitionParse fileName
            indexedModules <- if willVerify
                then lift $ mainVerify willChkAttr parsedDefinition
                else return Map.empty
            lift $ when willPrintDefinition
                $ if appKore
                    then putStrLn
                        $ unparseToString2
                        $ completeDefinition
                        $ toVerifiedDefinition indexedModules
                else putDoc (debug parsedDefinition)

            when (patternFileName /= "") $ do
                parsedPattern <- mainPatternParse patternFileName
                when willVerify $ do
                    indexedModule <-
                         lift $ lookupMainModule
                            (ModuleName mainModuleName)
                            indexedModules
                    _ <- mainPatternVerify indexedModule parsedPattern
                    return ()
                when willPrintPattern $
                    lift $ putDoc (debug parsedPattern)

-- | IO action that parses a kore definition from a filename and prints timing
-- information.
mainDefinitionParse :: String -> Main ParsedDefinition
mainDefinitionParse = mainParse parseKoreDefinition

-- | IO action that parses a kore pattern from a filename and prints timing
-- information.
mainPatternParse :: String -> Main ParsedPattern
mainPatternParse = mainParse parseKorePattern

-- | IO action verifies well-formedness of Kore definition and prints
-- timing information.
mainVerify
    :: Bool
    -- ^ whether to check (True) or ignore attributes during verification
    -> ParsedDefinition
    -- ^ Parsed definition to check well-formedness
    -> IO
        (Map.Map
            ModuleName
            (VerifiedModule StepperAttributes Attribute.Axiom)
        )
mainVerify willChkAttr definition =
    let attributesVerification =
            if willChkAttr
            then defaultAttributesVerification Proxy Proxy
            else DoNotVerifyAttributes
    in do
      verifyResult <-
          flip runReaderT Logger.emptyLogger
          . getLoggerT
          $ clockSomething "Verifying the definition"
            (verifyAndIndexDefinition
                attributesVerification
                Builtin.koreVerifiers
                definition
            )
      case verifyResult of
        Left err1            -> error (printError err1)
        Right indexedModules -> return indexedModules
