module Test.KoreJson (
    module Test.KoreJson,
) where

import Control.Monad (forever)
import Data.ByteString.Lazy qualified as BS
import Data.Char (isPrint)
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Kore.Attribute.Attributes (ParsedPattern)
import KoreJson
import Prelude.Kore hiding (Left, Right)

genKorePattern :: Gen KorePattern
genKorePattern =
    Gen.recursive
        Gen.choice
        [ KJEVar <$> genId <*> genSort
        , KJSVar <$> (('@' -:) <$> genId) <*> genSort
        , KJString <$> genPrintableAscii
        , KJTop <$> genSort
        , KJBottom <$> genSort
        , KJDv <$> genSort <*> genPrintableAscii
        ]
        [ do
            sorts <- between 1 10 genSort
            args <- exactly (length sorts - 1) genKorePattern
            name <- genId
            pure KJApp{name, sorts, args}
        , KJNot <$> genSort <*> genKorePattern
        , KJAnd <$> genSort <*> genKorePattern <*> genKorePattern
        , KJOr <$> genSort <*> genKorePattern <*> genKorePattern
        , KJImplies <$> genSort <*> genKorePattern <*> genKorePattern
        , KJIff <$> genSort <*> genKorePattern <*> genKorePattern
        , KJForall <$> genSort <*> genId <*> genSort <*> genKorePattern
        , KJExists <$> genSort <*> genId <*> genSort <*> genKorePattern
        , KJMu . ('@' -:) <$> genId <*> genSort <*> genKorePattern
        , KJNu . ('@' -:) <$> genId <*> genSort <*> genKorePattern
        , KJCeil <$> genSort <*> genSort <*> genKorePattern
        , KJFloor <$> genSort <*> genSort <*> genKorePattern
        , KJEquals <$> genSort <*> genSort <*> genKorePattern <*> genKorePattern
        , KJIn <$> genSort <*> genSort <*> genKorePattern <*> genKorePattern
        , KJNext <$> genSort <*> genKorePattern
        , KJRewrites <$> genSort <*> genKorePattern <*> genKorePattern
        ]

-- | special generator which yields "multi-X" patterns (breaks round-trip testing)
genMultiKorePattern :: Gen KorePattern
genMultiKorePattern =
    Gen.choice
        [ KJMultiOr
            <$> Gen.element [Left, Right]
            <*> genSort
            <*> between 3 12 (Gen.small genKorePattern)
        , KJMultiApp
            <$> Gen.element [Left, Right]
            <*> (Gen.element [('\\' -:), id] <*> genId)
            <*> exactly 2 genSort
            <*> between 3 12 (Gen.small genKorePattern)
        ]

(-:) :: Char -> Id -> Id
c -: (Id x) = Id $ T.cons c x

genAllKorePatterns :: Gen KorePattern
genAllKorePatterns =
    Gen.frequency [(21, genKorePattern), (2, genMultiKorePattern)]

genSort :: Gen Sort
genSort =
    Gen.recursive
        Gen.choice
        [SortVariable <$> genVarName]
        [Sort <$> genId <*> upTo 10 genSort]

genId :: Gen Id
genId =
    fmap Id $ (<>) <$> genVarName <*> Gen.text (Range.constant 0 5) Gen.digit

genVarName :: Gen Text
genVarName =
    T.cons <$> Gen.alpha <*> Gen.text (Range.linear 0 128) genIdChar

genIdChar :: Gen Char
genIdChar =
    Gen.frequency
        [ (10, Gen.alpha)
        , (3, Gen.digit)
        , (1, Gen.element "_'")
        ]

genPrintableAscii :: Gen Text
genPrintableAscii =
    T.filter isPrint <$> Gen.text (Range.linear 0 128) Gen.ascii

exactly :: Int -> Gen a -> Gen [a]
exactly n g
    | n >= 0 = Gen.list (Range.singleton n) g
    | otherwise = error "negative count requested"

upTo :: Int -> Gen a -> Gen [a]
upTo n g
    | n >= 0 = Gen.list (Range.linear 0 n) g
    | otherwise = error "negative range limit requested"

between :: Int -> Int -> Gen a -> Gen [a]
between n m g
    | n < 0 || m < 0 =
        error "negative range limits requested"
    | n <= m =
        Gen.list (Range.linear n m) g
    | otherwise =
        pure []

----------------------------------------
-- helper for the repl

showExamples :: IO a
showExamples =
    forever $ do
        korePattern <- Gen.sample genKorePattern
        BS.putStr $ encodeKoreJson korePattern
        void getLine

----------------------------------------
-- Tests

roundTripTests :: Group
roundTripTests =
    Group
        "Json -> KorePattern -> ParsedPattern Round trip tests"
        [ ("KorePattern -> json -> KorePattern", jsonRoundTrip)
        , ("KorePattern (no multi-things) -> ParsedPattern -> KorePattern", parsedRoundTrip)
        , ("ParsedPattern -> KorePattern -> KorePattern", korePatternRoundTrip)
        , ("json (valid, no multi-things) -> ParsedPattern -> json", fullRoundTrip)
        ]

jsonRoundTrip :: Property
jsonRoundTrip =
    property $ do
        korePattern <- forAll genAllKorePatterns
        -- this is testing To/FromJSON instances and lexical checks
        tripping korePattern encodeKoreJson decodeKoreJson

parsedRoundTrip :: Property
parsedRoundTrip =
    property $ do
        korePattern <- forAll genKorePattern
        -- testing KorePattern -> parsedPattern -> KorePattern
        -- where KorePattern is known to be valid

        -- This round trip fails on "MultiOr" and "MultiApp"
        -- constructs, as they introduce ambiguity.
        let convert :: KorePattern -> ParsedPattern
            convert = toParsedPattern `orFailWith` "toParsedPattern"
            parse :: ParsedPattern -> Either () KorePattern
            parse = pure . fromPattern
        tripping korePattern convert parse

korePatternRoundTrip :: Property
korePatternRoundTrip =
    property $ do
        korePattern <- forAll genAllKorePatterns
        -- testing ParsedPattern -> KorePattern -> ParsedPattern
        -- after producing ParsedPattern from KorePattern
        -- (we do not allow "Inhabitant" in ParsedPattern)
        let parsedP = toParsedPattern `orFailWith` "toParsedPattern" $ korePattern
        tripping parsedP fromPattern toParsedPattern

fullRoundTrip :: Property
fullRoundTrip =
    property $ do
        korePattern <- forAll genKorePattern
        -- testing Json -> parsedPattern -> Json
        -- after producing an initial json bytestring

        -- This round trip fails on "MultiOr" and "MultiApp"
        -- constructs, as they introduce ambiguity.

        let json = encodeKoreJson korePattern
            convert :: BS.ByteString -> ParsedPattern
            convert = decodePattern `orFailWith` "decodePattern"
            parse :: ParsedPattern -> Either () BS.ByteString
            parse = pure . encodePattern

        tripping json convert parse

orFailWith :: Show err => (a -> Either err b) -> String -> a -> b
parse `orFailWith` name = either failed id . parse
  where
    failed err = error $ "Error in " <> name <> ": " <> show err
