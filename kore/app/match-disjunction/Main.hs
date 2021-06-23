module Main (main) where

import Prelude.Kore
import GlobalMain (mainGlobal, ExeName (..))

exeName :: ExeName
exeName = ExeName "kore-match-disjunction"

data KoreMatchDisjunctionOptions =
    KoreMatchDisjunctionOptions
        { -- | Name of file containing a definition to verify and use for execution
          definitionFileName :: !FilePath
        , -- | Name of file containing a disjunction to verify and use for matching
          disjunctionFileName :: !FilePath
        , -- | Name of file used to match with disjunction
          matchFileName :: !FilePath
        , -- | Name for file to contain the output pattern
          outputFileName :: !(Maybe FilePath)
        , -- | The name of the main module in the definition
          mainModuleName :: !ModuleName
        }

parseKoreMatchDisjunctionOptions :: Parser KoreMatchDisjunctionOptions
parseKoreMatchDisjunctionOptions =
    KoreMatchDisjunctionOptions
        <$> argument
            str
            ( metavar "DEFINITION_FILE"
                <> help "Kore definition file to verify and use for execution"
            )
        <*> strOption
            ( metavar "DISJUNCTION_FILE"
                <> long "disjunction"
                <> help "TODO"
            )
        <*> strOption
            ( metavar "MATCH_FILE"
                <> long "match"
                <> help "TODO"
            )
        <*> optional
            ( strOption
                ( metavar "PATTERN_OUTPUT_FILE"
                    <> long "output"
                    <> help "Output file to contain final Kore pattern."
                )
            )
        <*> parseMainModuleName
  where
    parseMainModuleName =
        GlobalMain.parseModuleName
            "MODULE"
            "module"
            "The name of the main module in the Kore definition."


main :: IO ()
main = do
    options <-
        mainGlobal
            exeName
            Nothing
            undefined -- parseKoreMatchDisjunctionOptions
            undefined -- parserInfoModifiers
    undefined

