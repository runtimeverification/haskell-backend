module Data.Kore.Unparser.UnparseTest where

import           Data.Kore.AST
import           Data.Kore.ASTGen
import           Data.Kore.Parser.LexemeImpl
import           Data.Kore.Parser.ParserImpl
import           Data.Kore.Unparser.Unparse

import qualified Data.Attoparsec.ByteString.Char8 as Parser
import qualified Data.ByteString.Char8            as Char8
import           Test.Tasty
import           Test.Tasty.HUnit
import           Test.Tasty.QuickCheck

unparseParseTests :: TestTree
unparseParseTests =
    testGroup
        "QuickCheck Unparse&Parse Tests"
        [ testProperty "Object Id"
            (forAll (idGen Object) (unparseParseProp (idParser Object)))
        , testProperty "Meta Id"
            (forAll (idGen Meta) (unparseParseProp (idParser Meta)))
        , testProperty "StringLiteral"
            (forAll stringLiteralGen (unparseParseProp stringLiteralParser))
        , testProperty "Object SymbolOrAlias"
            (forAll (symbolOrAliasGen Object)
                (unparseParseProp (symbolOrAliasRawParser Object SymbolOrAlias))
            )
        , testProperty "Meta SymbolOrAlias"
            (forAll (symbolOrAliasGen Meta)
                (unparseParseProp (symbolOrAliasRawParser Meta SymbolOrAlias))
            )
        , testProperty "Object Symbol"
            (forAll (symbolGen Object) (unparseParseProp (symbolParser Object)))
        , testProperty "Meta Symbol"
            (forAll (symbolGen Meta) (unparseParseProp (symbolParser Meta)))
        , testProperty "Object Alias"
            (forAll (aliasGen Object) (unparseParseProp (aliasParser Object)))
        , testProperty "Meta Alias"
            (forAll (aliasGen Meta) (unparseParseProp (aliasParser Meta)))
        , testProperty "Object SortVariable"
            (forAll (sortVariableGen Object)
                (unparseParseProp (sortVariableParser Object))
            )
        , testProperty "Meta SortVariable"
            (forAll (sortVariableGen Meta)
                (unparseParseProp (sortVariableParser Meta))
            )
        , testProperty "Object Sort"
            (forAll (sortGen Object)
                (unparseParseProp (sortParser Object))
            )
        , testProperty "Meta Sort"
            (forAll (sortGen Meta)
                (unparseParseProp (sortParser Meta))
            )
        , testProperty "UnifiedVariable"
            (forAll unifiedVariableGen (unparseParseProp unifiedVariableParser))
--        , testProperty "UnifiedPattern"
--            (forAll unifiedPatternGen (unparseParseProp patternParser))
        ]

parse :: Parser.Parser a -> String -> Either String a
parse parser input = Parser.parseOnly (parser <* Parser.endOfInput) (Char8.pack input)

unparseParseProp :: (Unparse a, Eq a) => Parser.Parser a -> a -> Bool
unparseParseProp p a = parse p (unparseToString a) == Right a
