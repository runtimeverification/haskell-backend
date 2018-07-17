module Main where

import         Data.Semigroup ((<>))
import         Data.Text.Prettyprint.Doc ( LayoutOptions(..), PageWidth(..)
                                         , defaultLayoutOptions, layoutPretty
                                         , pretty )
import         Data.Text.Prettyprint.Doc.Render.Text (renderIO)
import         Options.Applicative
import         System.IO (stdout)

import         Data.Kore.Parser.Parser (fromKore)


data KoreFormatOptions =
    KoreFormatOptions
    { fileName :: FilePath  -- ^ file to unparse
    , width :: Int  -- ^ line width
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
        <> help "Line width [default: 80]" )


main :: IO ()
main =
    do let
          infoMod = fullDesc <> progDesc desc
            where
              desc = "Parse a Kore source file \
                     \and render it in standard format"
       KoreFormatOptions {..} <-
          execParser (info (commandLine <**> helper) infoMod)
       defn <- mainParse fromKore fileName
       let
          layoutOptions
              | width > 0 =
                  defaultLayoutOptions
                  { layoutPageWidth = AvailablePerLine width 1.0 }
              | otherwise =
                  defaultLayoutOptions { layoutPageWidth = Unbounded }
       renderIO stdout (layoutPretty layoutOptions $ pretty defn)

-- | Parse a Kore AST entity from a filename and prints timing information.
mainParse
    :: (FilePath -> String -> Either String a)
    -> FilePath
    -> IO a
mainParse parser fileName = do
    contents <- readFile fileName
    either error return (parser fileName contents)

