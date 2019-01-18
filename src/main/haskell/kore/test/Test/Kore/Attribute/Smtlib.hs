module Test.Kore.Attribute.Smtlib where

import           Data.Text
                 ( Text )
import qualified Data.Text as Text

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Sentence
import Kore.Attribute.Parser
import Kore.Attribute.Smtlib

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
    , "int_min"
    , "int_max"
    , "int_abs"
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

test_extracted :: [TestTree]
test_extracted =
    map test extracted
  where
    test arg =
        testCase caseName
            $ assertBool "expected successful parse"
            $ isRightAndJust $ parseSmtlib attrs
      where
        attrs = Attributes [ smtlibAttribute arg ]
        caseName = "[smtlib{}(\"" ++ Text.unpack arg ++ "\")]"

parseSmtlib :: Attributes -> Parser Smtlib
parseSmtlib = parseAttributes

isRightAndJust :: Parser Smtlib -> Bool
isRightAndJust =
    \case
        Right Smtlib { getSmtlib } ->
            case getSmtlib of
                Nothing -> False
                Just sExpr ->
                    seq sExpr True
        Left _ -> False
