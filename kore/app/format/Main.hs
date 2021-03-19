{-# LANGUAGE Strict #-}

module Main (main) where

import Prelude.Kore

import qualified Data.Text.IO as Text
import Options.Applicative
import System.IO
    ( stdout
    )

import Kore.Parser
    ( parseKoreDefinition
    )
import Kore.Syntax.Definition
    ( ParsedDefinition
    )
import Kore.Unparser
import Pretty
    ( LayoutOptions (..)
    , PageWidth (..)
    , defaultLayoutOptions
    , layoutPretty
    , renderIO
    )

import GlobalMain


data KoreFormatOptions =
    KoreFormatOptions
    { fileName :: FilePath  -- ^ file to unparse
    , width    :: Int  -- ^ line width
    }

commandLine :: Parser KoreFormatOptions
commandLine =
    KoreFormatOptions
    <$> argument str
        (  metavar "FILE"
        <> help "Kore source file to parse" )
    <*> option auto
        (  metavar "WIDTH"
        <> long "width"
        <> value 80
        <> help "Line width [default: 80; unlimited if WIDTH <= 0]" )

infoMod :: InfoMod options
infoMod =
    fullDesc
    <> progDesc "Parse a Kore definition and render it in standard format"
    <> header "kore-format - parse and render Kore definitions"

main :: IO ()
main =
    do
        options <-
            mainGlobal
                (ExeName "kore-format")
                Nothing  -- environment variable name for extra arguments
                commandLine
                infoMod
        case localOptions options of
            Nothing ->
                {-  Global options were parsed, but local options were not.
                    Exit gracefully. -}
                return ()
            Just KoreFormatOptions { fileName, width } ->
                do
                    defn <- readKoreOrDie fileName
                    let layoutOptions =
                            defaultLayoutOptions
                            { layoutPageWidth =
                                if width > 0
                                then AvailablePerLine width 1.0
                                else Unbounded
                            }
                    renderIO stdout (layoutPretty layoutOptions $ unparse defn)

-- | Read a 'KoreDefinition' from the given file name or signal an error.
readKoreOrDie :: FilePath -> IO ParsedDefinition
readKoreOrDie fileName =
    Text.readFile fileName
    >>= either error return . parseKoreDefinition fileName
