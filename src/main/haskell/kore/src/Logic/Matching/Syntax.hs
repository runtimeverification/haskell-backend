{-# OPTIONS_GHC -fno-warn-orphans #-}
{- |
Description: Concrete syntax of matching logic patterns

This module implements a parser and pretty-printer for the matching logic
pattern types in "Logic.Matching.Pattern" using a subset of the concrete syntax
of Kore, such as `\and{Bool}(A:Bool,B:Bool)` for a simple disjunction of
variables.
-}
module Logic.Matching.Syntax
    ( mlPattern
    , prettyPat
    , simpleSigPattern
    , simpleSigLabel
    , simpleSigSort
    ) where

import           Control.Applicative
import           Control.Monad
                 ( void )
import           Data.Functor.Foldable
                 ( Fix (Fix) )
import           Data.Reflection
import           Data.Text
                 ( Text )
import           Data.Text.Prettyprint.Doc
                 ( Doc, Pretty (..), (<>) )
import qualified Data.Text.Prettyprint.Doc as Doc
import           Data.Void
import           Text.Megaparsec hiding
                 ( some )
import           Text.Megaparsec.Char

import Logic.Matching.Pattern
import Logic.Matching.Signature.Simple

type Parser = Parsec Void Text

delimit :: Char -> Char -> Parser a -> Parser a
delimit l r = between (char l *> space) (char r *> space)

parens, braces :: Parser a -> Parser a
parens p = delimit '(' ')' p
braces p = delimit '{' '}' p

comma :: Parser ()
comma = char ',' *> space

mlPattern :: forall sort label var . Parser sort -> Parser label -> Parser var
          -> Parser (Pattern sort label var)
mlPattern pSort pLabel pVar = pat
  where
    pat = Fix <$> patF
    patF :: Parser (PatternF sort label var (Pattern sort label var))
    patF =
          alt "\\and" And sort1 (arg2 pat pat)
      <|> alt "\\not" Not sort1 (arg1 pat)
      <|> alt "\\exists" (uncurry . Exists) sort1 (arg2 annVar pat)
      <|> try (Application <$> pLabel <*> parens (sepBy pat comma))
      <|> uncurry Variable <$> annVar
    annVar :: Parser (sort, var)
    annVar = do v <- pVar; void $ char ':'; space; s <- pSort; return (s,v)
    sort1 :: Parser ((sort -> a) -> a)
    sort1 = arg1 pSort
    arg1 :: Parser a -> Parser ((a -> b) -> b)
    arg1 p = do x <- p; return (\f -> f x)
    arg2 :: Parser a -> Parser b -> Parser ((a -> b -> c) -> c)
    arg2 p1 p2 = do x <- p1; comma; y <- p2; return (\f -> f x y)
    alt :: Text -> a -> Parser (a -> b) -> Parser (b -> c) -> Parser c
    alt name con sortArgs args =
      (con <$ string name) <**> braces sortArgs <**> parens args

simpleSigPattern :: (Reifies sig ValidatedSignature)
                 => Parser Text -> Parser Text -> Parser var
                 -> Parser (WFPattern (SimpleSignature sig) var)
simpleSigPattern pSortName pLabelName pVar = do
  rawPat <- mlPattern pSortName pLabelName pVar
  case resolvePattern rawPat of
    Nothing -> fail "Unknown label or sort names"
    Just unsortedPat ->
      case checkSorts unsortedPat of
        Nothing     -> fail "Ill-sorted term"
        Just sorted -> return sorted

simpleSigLabel :: (Reifies sig ValidatedSignature)
               => Parser Text -> Parser (Label (SimpleSignature sig))
simpleSigLabel pName = do
  name <- pName
  case resolveLabel name of
    Just lbl -> return lbl
    Nothing  -> fail "Unknown label"

simpleSigSort :: (Reifies sig ValidatedSignature)
               => Parser Text -> Parser (Sort (SimpleSignature sig))
simpleSigSort pName = do
  name <- pName
  case resolveSort name of
    Just srt -> return srt
    Nothing  -> fail "Unknown label"

prettyPat :: (sort -> Doc ann) -> (label -> Doc ann) -> (var -> Doc ann) -> (child -> Doc ann)
          -> (PatternF sort label var child -> Doc ann)
prettyPat pSort pLabel pVar pChild = pPat
  where
    pPat pat = case pat of
      Variable s v -> pVar v <> Doc.colon <> pSort s
      Application l args -> pLabel l <> Doc.tupled (map pChild args)
      And s p1 p2 -> pretty ("\\and"::Text) <> Doc.braces (pSort s)
        <> Doc.parens (pChild p1 <> Doc.comma <> pChild p2)
      Not s p -> pretty ("\\not"::Text) <> Doc.braces (pSort s) <> Doc.parens (pChild p)
      Exists s _sVar v p ->
        pretty ("\\exists"::Text) <> Doc.braces (pSort s)
          <> Doc.parens (pVar v <> Doc.colon <> pSort s <> Doc.comma <> pChild p)

instance (Pretty sort, Pretty label, Pretty var, Pretty p)
      => Pretty (PatternF sort label var p) where
  pretty term = prettyPat pretty pretty pretty pretty term
