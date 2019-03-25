module Test.Kore.Attribute.Parser
    ( module Kore.Attribute.Parser
    , expectSuccess
    , expectFailure
    ) where

import Test.Tasty.HUnit

import Data.Either
       ( isLeft )

import Kore.AST.Sentence
       ( Attributes (..) )
import Kore.Attribute.Parser

expectSuccess
    :: (Eq attr, Eq e, Show attr, Show e)
    => attr
    -> Either e attr
    -> Assertion
expectSuccess assoc =
    assertEqual "expected parsed attribute" (Right assoc)

expectFailure :: Either e attr -> Assertion
expectFailure = assertBool "expected parse failure" . isLeft
