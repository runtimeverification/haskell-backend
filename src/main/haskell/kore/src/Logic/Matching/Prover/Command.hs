{-|
Description: Module for parsing, printing prover commands
-}
module Logic.Matching.Prover.Command where

import           Data.Text
                 ( Text )
import           Data.Text.Prettyprint.Doc
                 ( Pretty (pretty), colon, (<+>) )

import           Text.Megaparsec
import           Text.Megaparsec.Char


data Command ix rule formula
  = Add ix formula
  | Prove ix (rule ix)
  | AddAndProve ix formula (rule ix)
  | Undo | Show | Help
  deriving Show

-------------
-- Parsing --
type Parser = Parsec String String

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

parseUndo :: Parser (Command ix rule formula)
parseUndo = string "undo" >> return Undo

parseShow :: Parser (Command ix rule formula)
parseShow = string "show" >> return Show

parseHelp :: Parser (Command ix rule formula)
parseHelp = string "help" >> return Help


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
