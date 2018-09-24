{-| Description: Module for constructing, parsing, printing prover commands -}
module Logic.Matching.Prover.Command
    ( Command (..)
    , Parser
    , parseCommand
    ) where

import           Data.Text.Prettyprint.Doc
                 ( Pretty (..) )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Text.Megaparsec
import           Text.Megaparsec.Char

import Kore.Unparser

-- | Prover command data type
--   TODO: better way of expressing the inherent
--   differences between [Undo,Show,Help] and the other commands
data Command ix rule formula
  = Add ix formula
  | Prove ix (rule ix)
  | AddAndProve ix formula (rule ix)
  | Undo | Show | Help
  deriving Show

-------------
-- Parsing --
type Parser = Parsec String String

-- | parse 'add <ix>: <formula> [by <ml-rule>]'
parseAdd :: Parser ix -> Parser formula -> Parser (rule ix) -> Parser (Command ix rule formula)
parseAdd pIx pFormula pDerivation = do
  _ <- string "add"
  space
  ix <- pIx
  space >> char ':' >> space
  formula <- pFormula
  space
  option
    (Add ix formula)
    (AddAndProve ix formula <$ string "by" <* space <*> pDerivation)

-- | parse 'prove <ix> by <ml-rule>'
parseProve :: Parser ix -> Parser formula -> Parser (rule ix) -> Parser (Command ix rule formula)
parseProve pIx _ pDerivation = do
  _ <- string "prove"
  space
  ix <- pIx
  space
  _ <- string "by"
  space
  rule <- pDerivation
  return (Prove ix rule)

-- | parse 'undo'
parseUndo :: Parser (Command ix rule formula)
parseUndo = string "undo" >> return Undo

-- | parse 'show'
parseShow :: Parser (Command ix rule formula)
parseShow = string "show" >> return Show

-- | parse 'help'
parseHelp :: Parser (Command ix rule formula)
parseHelp = string "help" >> return Help


-- | main command parser
parseCommand :: Parser ix -> Parser formula -> Parser (rule ix) -> Parser (Command ix rule formula)
parseCommand pIx pFormula pDerivation
  =  parseProve pIx pFormula pDerivation
 <|> parseAdd pIx pFormula pDerivation
 <|> parseUndo
 <|> parseShow
 <|> parseHelp

--------------
-- Printing --
instance (Pretty ix, Unparse formula, Pretty (rule ix)) => Pretty (Command ix rule formula) where
    pretty =
        \case
            Add ix formula ->
                Pretty.sep [ "add", pretty ix, Pretty.colon, unparse formula ]
            Prove ix rule ->
                Pretty.sep
                    [ "prove", pretty ix, Pretty.colon
                    , "by", pretty rule
                    ]
            AddAndProve ix formula rule ->
                Pretty.sep
                    [ "add", pretty ix, Pretty.colon, unparse formula
                    , "by", pretty rule
                    ]
            Undo ->
                "undo"
            Show ->
                "show"
            Help ->
                "help"
