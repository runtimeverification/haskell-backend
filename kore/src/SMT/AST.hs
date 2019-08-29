{-|
Module      : SMT.AST
Description : AST for (parts of) the SMT commands
Copyright   : (c) Iavor S. Diatchki, 2014
              (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

Use the Smt* versions of data types to work with the SimpleSMT interface.
-}
module SMT.AST
  ( Constructor (..),
    ConstructorArgument (..),
    DataTypeDeclaration (..),
    FunctionDeclaration (..),
    SortDeclaration (..),
    SExpr (..),
    buildSExpr,
    parseSExpr,
    readSExpr,
    readSExprs,
    sendSExpr,
    showSExpr,
    nameFromSExpr,
    SmtConstructor,
    SmtConstructorArgument,
    SmtDataTypeDeclaration,
    SmtSortDeclaration,
    SmtFunctionDeclaration
    )
where

import Control.Applicative
  ( Alternative (..)
    )
import Control.DeepSeq
  ( NFData
    )
import Control.Monad.Fail
  ( MonadFail
    )
import Data.Char
  ( isSpace
    )
import Data.Maybe
  ( fromMaybe
    )
import Data.String
  ( IsString (..)
    )
import Data.Text
  ( Text
    )
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Data.Text.Internal.Builder
  ( Builder
    )
import qualified Data.Text.Internal.Builder as Text.Builder
import qualified Data.Text.Lazy as Text.Lazy
import Data.Void
  ( Void
    )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import System.IO
  ( Handle,
    hPutChar
    )
import Text.Megaparsec
  ( Parsec
    )
import qualified Text.Megaparsec as Parser
import qualified Text.Megaparsec.Char as Parser
import qualified Text.Megaparsec.Char.Lexer as Lexer

-- | S-expressions, the basic format for SMT-LIB 2.
data SExpr
  = Atom !Text
  | List ![SExpr]
  deriving (GHC.Generic, Eq, Ord, Show)

instance NFData SExpr

instance SOP.Generic SExpr

instance SOP.HasDatatypeInfo SExpr

instance IsString SExpr where
  fromString = Atom . Text.pack

{-| An argument to a data type constructor.

The name can be used as a getter in smt solvers. (Note: this is currently not
working due to a bug in z3 data type declaration,
see https://github.com/Z3Prover/z3/issues/2217 , also see the similar comment
in declareDatatypes in SimpleSMT.hs)
--}
data ConstructorArgument sort name
  = ConstructorArgument
      { name :: !name,
        argType :: !sort
        }
  deriving (Eq, Ord, Show)

{-| A data type constructor.
--}
data Constructor sort symbol name
  = Constructor
      { name :: !symbol,
        arguments :: ![ConstructorArgument sort name]
        }
  deriving (Eq, Ord, Show)

{-| A constructor-based data type declaration.

If the list of constructors is empty, the data type is empty.
--}
data DataTypeDeclaration sort symbol name
  = DataTypeDeclaration
      { name :: !name,
        typeArguments :: ![name],
        constructors :: ![Constructor sort symbol name]
        }
  deriving (Eq, Ord, Show)

-- | A non-constructor-based data type declaration.
data SortDeclaration name
  = SortDeclaration
      { name :: !name,
        arity :: Int
        }
  deriving (Eq, Ord, Show)

-- | A function declaration.
data FunctionDeclaration sort name
  = FunctionDeclaration
      { name :: !name,
        inputSorts :: ![sort],
        resultSort :: !sort
        }
  deriving (Eq, Ord, Show)

-- | Extracts the name from a sexpression denoting a named object.
nameFromSExpr :: SExpr -> Text
nameFromSExpr (Atom name) = name
nameFromSExpr (List (Atom name : _)) = name
nameFromSExpr e =
  (error . unlines)
    [ "Cannot extract name from s-expression.",
      "expression=" ++ showSExpr e
      ]

-- | Instantiate Constructor with the types needed by SimpleSMT.
type SmtConstructor = Constructor SExpr Text Text

-- | Instantiate ConstructorArgument with the types needed by SimpleSMT.
type SmtConstructorArgument = ConstructorArgument SExpr Text

-- | Instantiate DataTypeDeclaration with the types needed by SimpleSMT.
type SmtDataTypeDeclaration = DataTypeDeclaration SExpr Text Text

-- | Instantiate SortDeclaration with the types needed by SimpleSMT.
type SmtSortDeclaration = SortDeclaration Text

-- | Instantiate FunctionDeclaration with the types needed by SimpleSMT.
type SmtFunctionDeclaration = FunctionDeclaration SExpr Text

-- | Stream an S-expression into 'Builder'.
buildSExpr :: SExpr -> Builder
buildSExpr =
  \case
    Atom x -> Text.Builder.fromText x
    List es ->
      Text.Builder.singleton '('
        <> foldMap (\e -> buildSExpr e <> Text.Builder.singleton ' ') es
        <> Text.Builder.singleton ')'

-- | Show an S-expression.
showSExpr :: SExpr -> String
showSExpr = Text.Lazy.unpack . Text.Builder.toLazyText . buildSExpr

{- | Send an S-expression directly to a 'Handle'.

@sendSExpr@ performs slightly better than @buildSExpr@ by avoiding almost all
intermediate allocation.

@sendSExpr@ sends only the S-expression; it does not send the trailing newline
which signals the end of a command.

 -}
sendSExpr :: Handle -> SExpr -> IO ()
sendSExpr h = sendSExprWorker
  where
    sendSExprWorker =
      \case
        Atom atom -> Text.hPutStr h atom
        List atoms -> do
          hPutChar h '('
          mapM_ sendListElement atoms
          hPutChar h ')'
    sendListElement sExpr = do
      sendSExprWorker sExpr
      hPutChar h ' '

type Parser = Parsec Void Text

-- | Basic S-expression parser.
parseSExpr :: Parser SExpr
parseSExpr = parseAtom <|> parseList
  where
    parseAtom :: Parser SExpr
    parseAtom = lexeme (Atom <$> Parser.takeWhile1P Nothing notSpecial)
    parseList :: Parser SExpr
    parseList =
      List <$> (lparen *> Parser.many parseSExpr <* rparen)
    special :: Char -> Bool
    special c = isSpace c || c == '(' || c == ')' || c == ';'
    notSpecial :: Char -> Bool
    notSpecial = Prelude.not . special
    lparen :: Parser Char
    lparen = lexeme (Parser.char '(')
    rparen :: Parser Char
    rparen = lexeme (Parser.char ')')
    skipLineComment = Lexer.skipLineComment ";"
    space = Lexer.space Parser.space1 skipLineComment empty
    lexeme :: Parser a -> Parser a
    lexeme = Lexer.lexeme space

-- | Parse one S-expression.
readSExpr :: MonadFail m => Text -> m SExpr
readSExpr txt =
  case Parser.parse parseSExpr "<unknown>" txt of
    Left err -> fail (Parser.errorBundlePretty err)
    Right sExpr -> return sExpr

-- | Parse many S-expressions.
readSExprs :: Text -> [SExpr]
readSExprs txt =
  fromMaybe
    []
    (Parser.parseMaybe (Parser.some parseSExpr) txt)
