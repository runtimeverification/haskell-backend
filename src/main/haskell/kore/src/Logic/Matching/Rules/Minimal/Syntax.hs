{-# OPTIONS_GHC -fno-warn-orphans #-}
{-| Description: Concrete syntax for the minimal matching logic proof rules

Parser and pretty-printer for the minimal proof rules.
-}
module Logic.Matching.Rules.Minimal.Syntax
    ( parseId
    , parseMLRule
    ) where

import Control.Applicative
       ( some )
import Control.Monad
       ( void )
import Data.Char
       ( isAlphaNum )
import Data.Text
       ( Text )
import Data.Text.Prettyprint.Doc
       ( Doc, Pretty (pretty), sep, tupled, (<>) )
import Text.Megaparsec hiding
       ( some )
import Text.Megaparsec.Char

import Logic.Matching.Rules.Minimal

type Parser = Parsec String String

lexeme :: Parser a -> Parser a
lexeme p = p <* space

parens :: Parser a -> Parser a
parens = between (lexeme (char '(')) (lexeme (char ')'))

comma :: Parser ()
comma = char ',' >> space

number :: Parser Int
number = read <$> some digitChar

parsePathPos :: Parser [Int]
parsePathPos = sepBy number space1

--Todo: Remove these declarations in favor of Kore Parsers
parseId :: Parser String
parseId = lexeme $ takeWhile1P Nothing isAlphaNum

infixl 4 `arg`
arg :: Parser (a -> b) -> Parser a -> Parser b
arg l r = l <* comma <*> r

-- | Parse an rule of the minimal proof system,
-- given parsers for all the components
parseMLRule :: Parser label
            -> Parser var
            -> Parser term
            -> Parser ix
            -> Parser (MLRule label var term ix)
parseMLRule pLabel pVar pTerm pIx =
        propositionalRules
    <|> propagationRules
    <|> modusPonens
    <|> generalization
    <|> varsubst
    <|> forall
    <|> framing
    <|> existence
    <|> singvar
  where
    rule :: String -> Parser body -> Parser body
    rule name body = string name >> space >> parens body

    propositionalRules = try $ do
      void $ string "propositional"
      prop1 <|> prop2 <|> prop3

    prop1 = rule "1" $ Propositional1 <$> pTerm `arg` pTerm
    prop2 = rule "2" $ Propositional2 <$> pTerm `arg` pTerm `arg` pTerm
    prop3 = rule "3" $ Propositional3 <$> pTerm `arg` pTerm

    modusPonens = rule "mp" $
      ModusPonens <$> pIx `arg` pIx
    generalization = rule "ug" $
      Generalization <$> pVar `arg` pIx
    varsubst = rule "varsubst" $
      VariableSubstitution <$>
        (SubstitutedVariable <$> pVar)
        `arg` pTerm
        `arg` (SubstitutingVariable <$> pVar)
    forall = rule "forall" $
      ForallRule <$> pVar `arg` pTerm `arg` pTerm
    framing = rule "framing" $
      Framing <$> pLabel `arg` number `arg` pIx

    propagationRules = do
      void $ string "propagate-"
      propagateOr <|> propagateExists

    propagateOr = rule "or" $
      PropagateOr <$> pLabel `arg` number `arg` pTerm `arg` pTerm
    propagateExists = rule "exists" $
      PropagateExists <$> pLabel `arg` number `arg` pVar `arg` pTerm

    existence = rule "exists" $
      Existence <$> pVar
    singvar = rule "singvar" $
      Singvar <$> pVar `arg` pTerm `arg` parsePathPos `arg` parsePathPos

-- | Displays proof rules in the documented concrete syntax,
-- assuming pretty-printing instances for all the type parameters
instance (Pretty label, Pretty var, Pretty term, Pretty hyp)
       => Pretty (MLRule label var term hyp) where
  pretty proofRule = let
      rule :: Text -> [Doc ann] -> Doc ann
      rule prefix args = pretty prefix <> tupled args
    in case proofRule of
    Propositional1 p1 p2 -> rule "propositional1" [pretty p1,pretty p2]
    Propositional2 p1 p2 p3 -> rule "propositional2" [pretty p1,pretty p2,pretty p3]
    Propositional3 p1 p2 -> rule "propositional3" [pretty p1, pretty p2]
    ModusPonens h1 h2 -> rule "mp" [pretty h1,pretty h2]
    Generalization v h -> rule "ug" [pretty v,pretty h]
    VariableSubstitution (SubstitutedVariable x) h (SubstitutingVariable y) ->
      rule "varsubst" [pretty x,pretty h,pretty y]
    ForallRule v p1 p2 -> rule "forall" [pretty v,pretty p1,pretty p2]
    Framing lbl pos h -> rule "framing" [pretty lbl,pretty pos,pretty h]
    PropagateOr lbl pos p1 p2 -> rule "propagate-or" [pretty lbl,pretty pos,pretty p1,pretty p2]
    PropagateExists lbl pos x p -> rule "propagate-exists" [pretty lbl,pretty pos,pretty x,pretty p]
    Existence x -> rule "exists" [pretty x]
    Singvar v p path1 path2 -> rule "singvar" [pretty v,pretty p,sep (map pretty path1),sep (map pretty path2)]
