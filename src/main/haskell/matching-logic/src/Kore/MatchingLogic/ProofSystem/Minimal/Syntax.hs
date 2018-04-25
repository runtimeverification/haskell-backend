{-# LANGUAGE OverloadedStrings #-}
{-| Description: Parser and pretty-printer for the minimal proof system

Parser and pretty-printer for the minimal proof system.
-}
module Kore.MatchingLogic.ProofSystem.Minimal.Syntax
  ( parseId
  , parseMLRule
  , parseMLRuleSig)
  where
import           Control.Applicative                    (some)
import           Control.Monad.IO.Class                 (liftIO)
import           Control.Monad.State.Strict             (MonadState (..),
                                                         StateT, runStateT)
import           Data.Char                              (isAlphaNum, isSpace)
import           Data.Functor.Foldable                  (Fix (Fix))
import           Data.List                              (isPrefixOf, isSuffixOf)
import           Data.Text                              (Text)
import           Data.Void

import           Data.Text.Prettyprint.Doc              (Doc, Pretty (pretty),
                                                         sep, tupled, (<>))
import qualified Data.Text.Prettyprint.Doc              as Doc
import           Text.Megaparsec                        hiding (some)
import           Text.Megaparsec.Char

import qualified Kore.MatchingLogic.AST                 as AST
import           Kore.MatchingLogic.AST.Syntax          (mlPattern)
import           Kore.MatchingLogic.HilbertProof
import           Kore.MatchingLogic.ProofSystem.Minimal
import           Kore.MatchingLogic.Signature

type Parser = Parsec Void Text

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
parseId :: Parser Text
parseId = lexeme $ takeWhile1P Nothing isAlphaNum

infixl 4 `arg`
arg l r = l <* comma <*> r

-- | Parse an rule of the minimal proof system,
-- given parsers for all the components
parseMLRule :: Parser sort
            -> Parser label
            -> Parser var
            -> Parser term
            -> Parser ix
            -> Parser (MLRule sort label var term ix)
parseMLRule pSort pLabel pVar pTerm pIx =
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
    rule :: Text -> Parser body -> Parser body
    rule name body = string name >> space >> parens body

    propositionalRules = try $ do
      string "propositional"
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
      string "propagate-"
      propagateOr <|> propagateExists

    propagateOr = rule "or" $
      PropagateOr <$> pLabel `arg` number `arg` pTerm `arg` pTerm
    propagateExists = rule "exists" $
      PropagateExists <$> pLabel `arg` number `arg` pVar `arg` pTerm

    existence = rule "exists" $
      Existence <$> pVar
    singvar = rule "singvar" $
      Singvar <$> pVar `arg` pTerm `arg` parsePathPos `arg` parsePathPos

-- | Parse a rule of the minimal proof system
-- when the formula type is 'AST.SigPattern',
-- using the default pattern syntax over the provided
-- parsers for the sorts and labels of the signatures.
parseMLRuleSig :: forall sig var ix . (AST.IsSignature sig)
                  => Parser (Sort sig)
                  -> Parser (Label sig)
                  -> Parser var
                  -> Parser ix
                  -> Parser (MLRuleSig sig var ix)
parseMLRuleSig pSort pLabel pVar pIx =
    parseMLRule pSort pLabel pVar parseFormula pIx
  where
    parseFormula :: Parser (AST.WFPattern sig var)
    parseFormula = do
      term <- mlPattern pSort pLabel pVar
      case AST.checkSorts term of
        Nothing     -> fail "Ill-sorted term"
        Just wfTerm -> return wfTerm

-- | Displays proof rules in the documented concrete syntax,
-- assuming pretty-printing instances for all the type parameters
instance (Pretty sort, Pretty label, Pretty var, Pretty term, Pretty hyp)
       => Pretty (MLRule sort label var term hyp) where
  pretty p = let
      rule :: Text -> [Doc ann] -> Doc ann
      rule prefix args = pretty prefix <> tupled args
    in case p of
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
