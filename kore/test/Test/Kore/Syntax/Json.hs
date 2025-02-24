{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-x-partial #-} -- no head/tail warnings

module Test.Kore.Syntax.Json (
    -- Tasty wrappers
    test_JsonRoundTrips,
    test_Unit_tests_for_json_failure_modes,
    test_headerFailures,
    -- Hedgehog things
    roundTripTests,
    showExamples,
    writeExamples,
    -- generators
    genKorePattern,
    genMultiKorePattern,
    genAllKorePatterns,
) where

import Control.Monad (forever)
import Data.Bifunctor qualified as Bifunctor
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Char (isAlpha, isAlphaNum, isPrint)
import Data.List (isInfixOf, isPrefixOf)
import Data.List.NonEmpty qualified as NE
import Data.String (IsString)
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Kore.Attribute.Attributes (ParsedPattern)
import Kore.Syntax.Json
import Kore.Syntax.Json.Internal -- for testing and generating test data
import Prelude.Kore hiding (Left, Right, assert)
import Prelude.Kore qualified as Prelude
import System.Directory (createDirectoryIfMissing)
import System.FilePath ((<.>), (</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog
import Text.Printf (printf)

genKoreJson :: Gen KorePattern -> Gen KoreJson
genKoreJson = fmap (KoreJson KORE KJ1)

genKorePattern :: Gen KorePattern
genKorePattern =
    Gen.recursive
        Gen.choice
        [ KJEVar <$> genId <*> genSort
        , KJSVar <$> (('@' -:) <$> genId) <*> genSort
        , KJString <$> genStringLiteral
        , KJTop <$> genSort
        , KJBottom <$> genSort
        , KJDV <$> genSort <*> genStringLiteral
        ]
        [ do
            sorts <- between 1 10 genSort
            args <- exactly (length sorts - 1) genKorePattern
            name <- (Gen.element [('\\' -:), id] <*> genId)
            pure KJApp{name, sorts, args}
        , KJNot <$> genSort <*> genKorePattern
        , KJAnd <$> genSort <*> between 2 10 genKorePattern
        , KJOr <$> genSort <*> between 2 10 genKorePattern
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
            <*> (NE.fromList <$> between 3 12 (Gen.small genAllKorePatterns))
        , KJLeftAssoc
            <$> (Gen.element [('\\' -:), id] <*> genId)
            <*> exactly 2 genSort
            <*> (NE.fromList <$> between 3 12 (Gen.small genAllKorePatterns))
        , KJRightAssoc
            <$> (Gen.element [('\\' -:), id] <*> genId)
            <*> exactly 2 genSort
            <*> (NE.fromList <$> between 3 12 (Gen.small genAllKorePatterns))
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
        [SortVar <$> genId]
        [SortApp <$> genId <*> upTo 10 genSort]

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
        , (1, Gen.element ['-', '\''])
        ]

genStringLiteral :: Gen Text
genStringLiteral =
    fmap T.concat $
        Gen.list (Range.linear 0 32) $
            Gen.text (Range.linear 0 128) Gen.latin1

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
-- helpers for the repl

showExamples :: IO ()
showExamples =
    forever $ do
        koreJson <- Gen.sample (genKoreJson genKorePattern)
        BS.putStr $ encodeKoreJson koreJson
        void getLine

writeExamples :: Bool -> FilePath -> FilePath -> Int -> IO ()
writeExamples withMultiThings dir basename n
    | n <= 0 =
        error $ unwords ["Requested", show n, "<=0 examples, nothing to do."]
    | n >= 100 =
        error "Cowardly refusing to create more than 99 files."
    | otherwise =
        do
            createDirectoryIfMissing False dir
            mapM_ generateFile [1 .. n]
  where
    generateFile :: Int -> IO ()
    generateFile i =
        Gen.sample (genKoreJson generator)
            >>= BS.writeFile (file i) . encodeKoreJson

    generator =
        if withMultiThings then genAllKorePatterns else genKorePattern

    file i = dir </> basename ++ printf "_%02d" i <.> "json"

----------------------------------------
-- Tests

-- Tasty interface, whole group only
test_JsonRoundTrips :: [TestTree]
test_JsonRoundTrips =
    [ testProperty "KorePattern -> json -> KorePattern" jsonRoundTrip
    , testProperty "KorePattern (no multi-things) -> ParsedPattern -> KorePattern" parsedRoundTrip
    , testProperty "ParsedPattern -> KorePattern -> KorePattern" korePatternRoundTrip
    , testProperty "json (valid, no multi-things) -> ParsedPattern -> json" fullRoundTrip
    ]

roundTripTests :: Group
roundTripTests = roundTripTestsWith 1000

roundTripTestsWith :: TestLimit -> Group
roundTripTestsWith n =
    Group
        "Json -> KorePattern -> ParsedPattern Round trip tests"
        [ ("KorePattern -> json -> KorePattern", withTests n jsonRoundTrip)
        , ("KorePattern (no multi-things) -> ParsedPattern -> KorePattern", withTests n parsedRoundTrip)
        , ("ParsedPattern -> KorePattern -> KorePattern", withTests n korePatternRoundTrip)
        , ("json (valid, no multi-things) -> ParsedPattern -> json", withTests n fullRoundTrip)
        ]

jsonRoundTrip :: Property
jsonRoundTrip =
    property $ do
        koreJson <- forAll $ genKoreJson genAllKorePatterns
        -- this is testing To/FromJSON instances and lexical checks
        tripping koreJson encodeKoreJson decodeKoreJson

parsedRoundTrip :: Property
parsedRoundTrip =
    property $ do
        korePattern <- forAll genKorePattern
        -- testing KorePattern -> parsedPattern -> KorePattern
        -- where KorePattern is known to be valid

        -- This round trip fails on "MultiOr" and "MultiApp"
        -- constructs, as they introduce ambiguity.
        let parse :: ParsedPattern -> Either () KorePattern
            parse = pure . fromPattern
        tripping korePattern toParsedPattern parse

korePatternRoundTrip :: Property
korePatternRoundTrip =
    property $ do
        korePattern <- forAll genAllKorePatterns
        -- testing ParsedPattern -> KorePattern -> ParsedPattern
        -- after producing ParsedPattern from KorePattern
        -- (we do not allow "Inhabitant" in ParsedPattern)
        let parsedP = toParsedPattern korePattern
            parse :: KorePattern -> Either () ParsedPattern
            parse = pure . toParsedPattern
        tripping parsedP fromPattern parse

fullRoundTrip :: Property
fullRoundTrip =
    property $ do
        koreJson <- forAll $ genKoreJson genKorePattern
        -- testing Json -> parsedPattern -> Json
        -- after producing an initial json bytestring

        -- This round trip fails on "MultiOr" and "MultiApp"
        -- constructs, as they introduce ambiguity.

        let json = encodeKoreJson koreJson
            convert :: BS.ByteString -> ParsedPattern
            convert = decodePattern `orFailWith` "decodePattern"
            parse :: ParsedPattern -> Either () BS.ByteString
            parse = pure . encodePattern

        tripping json convert parse

orFailWith :: Show err => (a -> Either err b) -> String -> a -> b
parse `orFailWith` name = either failed id . parse
  where
    failed err = error $ "Error in " <> name <> ": " <> show err

----------------------------------------
-- unit tests for specific properties

test_Unit_tests_for_json_failure_modes :: [TestTree]
test_Unit_tests_for_json_failure_modes =
    [ eVarChecks
    , sVarChecks
    ]

-- lexical check for identifiers
eVarChecks :: TestTree
eVarChecks =
    testGroup
        "Element variable lexical checks"
        [ testProperty "A set variable name must not be empty" testNotEmpty
        , testProperty "A valid element variable is accepted" $
            property $ do
                Id valid <- forAll genId
                diff (checkIdChars valid) (==) []
        , testProperty "A variable name has to start by a character" $
            withTests 1000 testEVarInitial
        , testProperty "A variable name must not contain non-alphanumeric characters" $
            withTests 1000 testEVarCharSet
        ]

testNotEmpty :: Property
testNotEmpty =
    withTests 1 . property $ diff (checkIdChars T.empty) (==) ["Empty"]

testEVarInitial :: Property
testEVarInitial =
    property $
        do
            Id valid <- forAll genId

            notLetter <- forAll $ Gen.filter (not . isAlpha) Gen.ascii
            let nonLetterStart = checkIdChars $ T.cons notLetter valid
            length nonLetterStart === 1
            assert ("Illegal initial character" `isPrefixOf` head nonLetterStart)

            notPrintable <- forAll $ Gen.filter (not . isPrint) Gen.ascii
            let nonPrintableStart = checkIdChars $ T.cons notPrintable valid
            length nonPrintableStart === 1
            assert ("Illegal initial character" `isPrefixOf` head nonLetterStart)

testEVarCharSet :: Property
testEVarCharSet =
    property $
        do
            initial <- forAll Gen.alpha
            notAlphaNum <- forAll $ Gen.filter (not . isAllowedChar) Gen.ascii
            let nonAlphaNumChars = checkIdChars $ T.pack [initial, notAlphaNum]
            length nonAlphaNumChars === 1
            assert ("Contains illegal characters: " `isPrefixOf` head nonAlphaNumChars)

isAllowedChar :: Char -> Bool
isAllowedChar c = isAlphaNum c || c `elem` ['-', '\'']

sVarChecks :: TestTree
sVarChecks =
    testGroup
        "Set variable lexical checks"
        [ testProperty "A valid set variable is accepted" $
            property $ do
                Id valid <- forAll genId
                diff (checkSVarName $ T.cons '@' valid) (==) []
        , testProperty
            "A set variable name has to start by `@'"
            testSVarInitial
        , testProperty
            "A set variable must be a valid identifier after the `@'"
            testSVarSuffix
        ]

testSVarInitial :: Property
testSVarInitial =
    property $
        do
            wrongInitial <- forAll $ Gen.filter (/= '@') Gen.ascii
            Id valid <- forAll genId
            let withWrongInitial = checkSVarName $ T.cons wrongInitial valid
            withWrongInitial === ["Must start with `@'"]

testSVarSuffix :: Property
testSVarSuffix =
    property $
        do
            notAlphaNum <- forAll $ Gen.filter (not . isAllowedChar) Gen.ascii
            let withWrongSuffix = checkSVarName $ T.pack ['@', 'X', notAlphaNum]
            length withWrongSuffix === 1
            assert ("Contains illegal characters: " `isPrefixOf` head withWrongSuffix)

----------------------------------------

test_headerFailures :: TestTree
test_headerFailures =
    testGroup "Header (format and version) checks" $
        map (uncurry testProperty) headerTests

headerTests :: IsString name => [(name, Property)]
headerTests =
    map
        (Bifunctor.second (withTests 1 . property))
        [
            ( "Correct test data parses"
            , assert . isRight $
                decodeKoreJson $
                    withHeader "KORE" "1" aString
            )
        ,
            ( "Format string errors are reported"
            , diffLeft "Error in $.format: expected \"KORE\"" $
                decodeKoreJson $
                    withHeader "Gore" "1" aString
            )
        ,
            ( "Version string errors are reported"
            , diffLeft "Error in $.version: expected 1.0" $
                decodeKoreJson $
                    withHeader "KORE" "2" aString
            )
        ,
            ( "Payload errors are reported"
            , expectLeft ("key \"tag\" not found" `isInfixOf`) $
                decodeKoreJson $
                    withHeader "KORE" "1" rubbish
            )
        ,
            ( "Format errors take precedence"
            , diffLeft "Error in $.format: expected \"KORE\"" $
                decodeKoreJson $
                    withHeader "Gore" "42" rubbish
            )
        ,
            ( "Version errors take precedence"
            , diffLeft "Error in $.version: expected 1.0" $
                decodeKoreJson $
                    withHeader "KORE" "42" rubbish
                    -- NB if the payload is not an object, the version
                    -- error does _not_ take precedence!
            )
        ]
  where
    rubbish = "{ \"rubbish\": 42 }"

diffLeft ::
    (MonadTest m, Eq a, Eq b, Show a, Show b) =>
    a ->
    Either a b ->
    m ()
diffLeft expected result =
    diff result (==) (Prelude.Left expected)

expectLeft ::
    (MonadTest m, MonadFail m, Show b) =>
    (a -> Bool) ->
    Either a b ->
    m ()
expectLeft predicate = \case
    Prelude.Left a -> assert $ predicate a
    Prelude.Right x -> fail $ "Unexpected " <> show x

withHeader :: BS.ByteString -> BS.ByteString -> BS.ByteString -> BS.ByteString
withHeader format version payload =
    BS.unlines
        [ "{"
        , "  \"format\": \"" <> format <> "\","
        , "  \"version\": " <> version <> ","
        , "  \"term\": " <> payload
        , "}"
        ]

aString :: BS.ByteString
aString =
    BS.unlines
        [ "  {"
        , "    \"tag\": \"String\","
        , "    \"value\": \"parse me!\""
        , "  }"
        ]
