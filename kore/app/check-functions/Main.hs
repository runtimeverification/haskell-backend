module Main (main) where

import qualified Data.Text.IO as Text
import GlobalMain
import Kore.Options
import Kore.Parser (parseKoreDefinition)
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
        case parseKoreDefinition fileName file of
            Left msg -> error msg
            Right _ -> return ()
