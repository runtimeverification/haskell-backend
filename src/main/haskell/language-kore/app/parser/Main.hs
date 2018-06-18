{-# LANGUAGE  NamedFieldPuns #-}

module Main where

import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.Error
import           Data.Kore.Parser.Parser                    (fromKore)
import           Data.Kore.AST.Sentence                     (KoreDefinition)

import           Control.Exception                          (evaluate)
import           Control.Monad                              (when)
import           System.Clock                               (Clock (Monotonic)
                                                            ,diffTimeSpec
                                                            ,getTime)

import           Options.Applicative
import           Data.Semigroup                             ((<>))

{-
Main module to run kore-parser
TODO: add command line argument tab-completion
-}

-- | Main options record
data KoreParserOptions = KoreParserOptions
    { fileName    :: !String -- ^ Filename to parse and verify
    , willPrint   :: !Bool   -- ^ Option to print definition
    , willVerify  :: !Bool   -- ^ Option to verify definition
    , willChkAttr :: !Bool   -- ^ Option to check attributes during verification
    }

-- | Command Line Argument Parser
commandLineParser :: Parser KoreParserOptions
commandLineParser =
    KoreParserOptions
    <$> argument str
        (  metavar "FILE"
        <> help "Kore source file to parse [and verify]" )
    <*> switch3 "print"
        "Print parsed definition to stdout [default]"
        "Do not print parsed definition to stdout"
    <*> switch3 "verify"
            "Verify well-formedness of parsed definition [default]"
            "Do not verify well-formedness of parsed definition"
    <*> switch3 "chkattr"
            "Check attributes during verification [default]"
            "Ignore attributes during verification"

-- | Run argument parser for kore-parser
commandLineParse :: IO KoreParserOptions
commandLineParse = execParser opts
    where
      opts = info
             ( commandLineParser <**> helper )
             (  fullDesc
             <> progDesc "Parses Kore definition in FILE; optionally, \
                         \Verifies well-formedness"
             <> header "kore-parser - a parser for Kore definitions" )


main :: IO ()
main =
    do {
    ; KoreParserOptions
      { fileName    = fileName
      , willPrint   = willPrint
      , willVerify  = willVerify
      , willChkAttr = willChkAttr
      } <- commandLineParse
    ; contents <-
        clockSomethingIO "Reading the input file" (readFile fileName)
    ; parseResult <-
        clockSomething "Parsing the file" (fromKore fileName contents)
    ; let parsedDefinition =
            case parseResult of
                Left err         -> error err
                Right definition -> definition
    ; when (willVerify) (verifyMain willChkAttr parsedDefinition)
    ; when (willPrint) (print parsedDefinition)
    }

{-|
IO subprocess to verify well-formedness of Kore definition
Bool argument determines if attributes are checked (True), or ignored.
-}
verifyMain :: Bool -> KoreDefinition -> IO ()
verifyMain willChkAttr definition =
    let attributesVerification =
            if willChkAttr
            then case defaultAttributesVerification of
                    Left err           -> error (printError err)
                    Right verification -> verification
            else DoNotVerifyAttributes
    in do {
       ; verifyResult <-
            clockSomething
       "Verifying the definition"
                ( verifyDefinition
                  attributesVerification
                  definition )
      ; case verifyResult of
            Left err1 -> error (printError err1)
            Right _   -> return ()
      }


----------------------
-- Helper Functions --

{-|
Parser builder to create a boolean argument,
with a positive and negative 'flag'
and default value (True)
-}
switch3 ::
    String -> -- ^ flag name
    String -> -- ^ Positive help text
    String -> -- ^ Negative help text
    Parser Bool
switch3 longName posHelpText negHelpText =
    flag' False
        (  long ("no"++longName)
        <> help negHelpText )
    <|> flag True True  -- first argument to 'flag' is the default
        (  long longName
        <> help posHelpText )


-- | Time a pure computation and print results.
clockSomething :: String -> a -> IO a
clockSomething description something =
    clockSomethingIO description (evaluate something)


-- | Time an IO computation and print results.
clockSomethingIO :: String -> IO a -> IO a
clockSomethingIO description something = do
    start <- getTime Monotonic
    x <- something
    end <- getTime Monotonic
    putStrLn (description ++" "++ show (diffTimeSpec end start))
    return x
