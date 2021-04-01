{-# LANGUAGE Strict #-}

module Test.Kore.Attribute.Smtlib (
    test_extracted_smtlib,
    test_extracted_smthook,
    test_fill_SExpr_templates,
) where

import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import Kore.Attribute.Parser
import Kore.Attribute.Smthook
import Kore.Attribute.Smtlib
import Prelude.Kore
import Test.Tasty
import Test.Tasty.HUnit

-- | A list of arguments to @smtlib@, extracted from the K distribution
extracted :: [Text]
extracted =
    [ "smt_seq_concat"
    , "smt_seq_nil"
    , "not"
    , "and"
    , "and"
    , "xor"
    , "or"
    , "or"
    , "=>"
    , "="
    , "distinct"
    , "^"
    , "(mod (^ #1 #2) #3)"
    , "*"
    , "div"
    , "mod"
    , "div"
    , "mod"
    , "+"
    , "-"
    , "(ite (< #1 #2) #1 #2)"
    , "(ite (< #1 #2) #2 #1)"
    , "(ite (< #1 0) (- 0 #1) #1)"
    , "<="
    , "<"
    , ">="
    , ">"
    , "="
    , "distinct"
    , "(not (== #1 #1))"
    , "-"
    , "(* roundNearestTiesToEven #1 #2)"
    , "(/ roundNearestTiesToEven #1 #2)"
    , "(remainder roundNearestTiesToEven #1 #2)"
    , "(+ roundNearestTiesToEven #1 #2)"
    , "(- roundNearestTiesToEven #1 #2)"
    , "abs"
    , "max"
    , "min"
    , "<="
    , "<"
    , ">="
    , ">"
    , "=="
    , "(not (== #1 #2))"
    , "="
    , "distinct"
    , "ite"
    ]

test_extracted_smtlib :: [TestTree]
test_extracted_smtlib =
    map test extracted
  where
    test arg =
        testCase caseName $
            assertBool "expected successful parse" $
                isRightAndJust $ parseSmtlib attrs
      where
        attrs = Attributes [smtlibAttribute arg]
        caseName = "[smtlib{}(\"" ++ Text.unpack arg ++ "\")]"

parseSmtlib :: Attributes -> Parser Smtlib
parseSmtlib = parseAttributes

isRightAndJust :: Parser Smtlib -> Bool
isRightAndJust =
    \case
        Right Smtlib{getSmtlib} ->
            case getSmtlib of
                Nothing -> False
                Just sExpr ->
                    seq sExpr True
        Left _ -> False

test_extracted_smthook :: [TestTree]
test_extracted_smthook =
    map test extracted
  where
    test arg =
        testCase caseName $
            assertBool "expected successful parse" $
                isSmthookRightAndJust $ parseSmthook attrs
      where
        attrs = Attributes [smthookAttribute arg]
        caseName = "[smt-hook{}(\"" ++ Text.unpack arg ++ "\")]"

test_fill_SExpr_templates :: TestTree
test_fill_SExpr_templates =
    testCase "applySExpr atom [1, 2] == applySExpr (atom #1 #2) [1, 2]" $
        assertBool "" $
            (==) left right
  where
    left = applySExpr (Atom "atom") arguments
    right = applySExpr (List [Atom "atom", Atom "#1", Atom "#2"]) arguments
    arguments = [Atom "1", Atom "2"]

parseSmthook :: Attributes -> Parser Smthook
parseSmthook = parseAttributes

isSmthookRightAndJust :: Parser Smthook -> Bool
isSmthookRightAndJust =
    \case
        Right Smthook{getSmthook} ->
            case getSmthook of
                Nothing -> False
                Just sExpr ->
                    seq sExpr True
        Left _ -> False
