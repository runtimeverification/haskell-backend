module CLIParser
    ( KoreParserOpts(..)
    , cliParse
    ) where

import           Options.Applicative
import           Data.Semigroup                           ((<>))


data KoreParserOpts = KoreParserOpts
    { fileName    :: String
    , willPrint   :: Bool
    , willVerify  :: Bool
    , willChkAttr :: Bool
    }



{-| Command Line Argument Parser -}
cliParser :: Parser KoreParserOpts
cliParser = KoreParserOpts
      <$> argument str
              ( metavar "FILE"
              <> help "Kore source file to parse [and verify]" )
      <*> switch3 "print"
              "Print parsed definition to stdout" 
              "Do not print parsed definition to stdout" 
      <*> switch3 "verify"
              "Verify well-formedness of parsed definition"
              "Do not verify well-formedness of parsed definition" 
      <*> switch3 "chkattr"
              "Check attributes during verification"
              "Ignore attributes during verification"

cliParse = execParser opts
  where
    opts = info (cliParser <**> helper)
      ( fullDesc
     <> progDesc "Parses Kore definition in FILE; optionally, Verifies well-formedness"
     <> header "kore-parser - a parser for Kore definitions" )


{-| Helper parser builder to create a 3 way boolean argument, with a positive, negative, and default flag -}
switch3 longName posHelpText negHelpText =
    flag' False
            ( long ("no"++longName)
            <> help negHelpText )
    <|> flag True True
            ( long longName
            <> help posHelpText )
