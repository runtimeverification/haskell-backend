{-| Description: Module for constructing, parsing, printing prover commands -}
module Logic.Matching.Prover.Command
  (Command(..), Parser, parseCommand,)
where

import Data.Text
       ( Text )
import Data.Text.Prettyprint.Doc
       ( Pretty (pretty), colon, (<+>) )

import Text.Megaparsec
import Text.Megaparsec.Char

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
instance (Pretty ix, Pretty formula, Pretty (rule ix)) => Pretty (Command ix rule formula) where
  pretty (Add ix formula)              =  pretty(  "add"::Text)<+>pretty ix<+>colon<+>pretty formula
  pretty (Prove ix rule)               =  pretty("prove"::Text)<+>pretty ix<+>colon
                                      <+> pretty(   "by"::Text)<+>pretty rule
  pretty (AddAndProve ix formula rule) =  pretty(  "add"::Text)<+>pretty ix<+>colon<+>pretty formula
                                      <+> pretty(   "by"::Text)<+>pretty rule
  pretty Undo                          =  pretty( "undo"::Text)
  pretty Show                          =  pretty( "show"::Text)
  pretty Help                          =  pretty( "help"::Text)
