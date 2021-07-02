module Main (main) where

import qualified Data.Text.IO as Text
import GlobalMain
import Kore.Attribute.Function (
    isDeclaredFunction,
 )
import Kore.Attribute.Pattern.Function (
    isFunction,
 )
import Kore.Equation (
    Equation (Equation),
    right,
 )
import Kore.Equation.Sentence (
    fromSentenceAxiom,
 )
import Kore.Internal.TermLike (
    isFunctionPattern,
 )
import Kore.Options (
    InfoMod,
    Parser,
    argument,
    fullDesc,
    header,
    help,
    metavar,
    progDesc,
    str,
 )
import Kore.Parser (
    parseKoreDefinition,
 )
import Kore.Syntax.Definition (
    definitionModules,
 )
import Kore.Syntax.Module (
    Module (..),
 )
import Kore.Syntax.Sentence (
    projectSentenceAxiom,
    sentenceAxiomAttributes,
    sentenceAxiomPattern,
 )
import Prelude.Kore

-- | modifiers for the command line parser description
checkerInfoModifiers :: InfoMod options
checkerInfoModifiers =
    fullDesc
        <> progDesc
            "Checks function definitions in FILE and verifies that for every \
            \equation in a function definition, the right-hand side of the \
            \equation is a function pattern."
        <> header "kore-check-functions - a tool to check function definitions"

newtype KoreCheckerOptions = KoreCheckerOptions
    { -- | Name for a file containing function definitions to verify.
      fileName :: FilePath
    }

parseKoreCheckerOptions :: Parser KoreCheckerOptions
parseKoreCheckerOptions =
    KoreCheckerOptions
        <$> argument
            str
            ( metavar "FILE"
                <> help "Kore source file to check."
            )

main :: IO ()
main = do
    options <-
        mainGlobal
            (ExeName "kore-check-functions")
            Nothing -- environment variable name for extra arguments
            parseKoreCheckerOptions
            checkerInfoModifiers
    forM_ (localOptions options) $ \KoreCheckerOptions{fileName} -> do
        file <- Text.readFile fileName
        mods <- case parseKoreDefinition fileName file of
            Left msg -> error msg
            Right defn -> return $ definitionModules defn
        forM_ (mods >>= moduleSentences) $ \sentence ->
            forM_ (projectSentenceAxiom sentence) $ \sentenceAxiom -> do
                -- need to verify sentenceAxiom
                case fromSentenceAxiom (attrs, verified) of
                    Right Equation{right}
                        | not (isFunctionPattern right) -> error "Function check fail."
                    Right _ -> return ()
                    Left _ -> error "fromSentenceAxiom error" -- need to correctly handle errors
