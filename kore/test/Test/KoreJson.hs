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
        [ KJEVar <$> genId Nothing <*> genSort
        , KJSVar <$> (genId (Just '@')) <*> genSort
        , KJString <$> genPrintableAscii
        , KJDomainValue <$> genSort <*> genPrintableAscii
        ]
        $ map genConn [minBound .. maxBound]
            <> [ KJQuantifier
                    <$> Gen.element [Forall, Exists]
                    <*> genSort
                    <*> genId Nothing
                    <*> genSort
                    <*> genKorePattern
               , KJFixpoint
                    <$> Gen.element [Mu, Nu]
                    <*> genId (Just '@')
                    <*> genSort
                    <*> genKorePattern
               , genApp
               ]
            <> zipWith genPred [minBound .. maxBound] [1, 1, 2, 2]
            <> [ KJNext <$> genSort <*> genKorePattern
               , KJRewrites <$> genSort <*> genKorePattern <*> genKorePattern
               , KJMultiOr <$> Gen.element [Left, Right] <*> genSort <*> between 3 12 genKorePattern
               , KJMultiApp <$> Gen.element [Left, Right] <*> genId (Just '\\') <*> exactly 3 genSort <*> between 3 12 genKorePattern
               ]
  where
    genApp :: Gen KorePattern
    genApp = do
        sorts <- between 1 10 genSort
        args <- exactly (length sorts - 1) genKorePattern
        name <- genId Nothing
        pure KJApp{name, sorts, args}

    genConn :: Connective -> Gen KorePattern
    genConn c =
        KJConnective c
            <$> genSort
            <*> exactly (arity c) genKorePattern
    -- makes sure valid argument counts are generated

    arity :: Connective -> Int
    arity Top = 0
    arity Bottom = 0
    arity Not = 1
    arity And = 2
    arity Or = 2
    arity Iff = 2
    arity Implies = 2

    genPred :: Pred -> Int -> Gen KorePattern
    genPred p n =
        KJPredicate p <$> genSort <*> genSort <*> exactly n genKorePattern

genSort :: Gen Sort
genSort =
    Gen.recursive
        Gen.choice
        [SortVariable <$> genVarName]
        [Sort <$> genId Nothing <*> upTo 10 genSort]

genId :: Maybe Char -> Gen Id
genId optChar =
    fmap Id $ (<>) <$> genName <*> genDigits
  where
    genName = maybe id T.cons optChar <$> genVarName
    genDigits = Gen.text (Range.constant 0 5) Gen.digit

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

jsonRoundTrip :: Property
jsonRoundTrip =
    property $ do
        korePattern <- forAll genKorePattern
        -- this is testing To/FromJSON instances
        tripping korePattern encodeKoreJson decodeKoreJson

parserRoundTrip :: Property
parserRoundTrip =
    property $ do
        korePattern <- forAll genKorePattern
        -- testing KorePattern -> parsedPattern -> KorePattern
        -- where KorePattern is known to be valid

        -- This round trip fails on "MultiOr" and "MultiApp"
        -- constructs, as they introduce ambiguity.
        -- let convert :: KorePattern -> ParsedPattern
        --     convert = either (error . show) id . toParsedPattern
        --     parse :: ParsedPattern -> Either () KorePattern
        --     parse = pure . fromPattern
        -- tripping korePattern convert parse

        -- testing ParsedPattern -> KorePattern -> ParsedPattern
        -- after producing ParsedPattern from KorePattern
        -- (we do not allow "Inhabitant" in ParsedPattern)
        let parsedP =
                either (error . show) id $
                    toParsedPattern korePattern
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
            convert = either (error . show) id . decodePattern
            parse :: ParsedPattern -> Either () BS.ByteString
            parse = pure . encodePattern

        tripping json convert parse
