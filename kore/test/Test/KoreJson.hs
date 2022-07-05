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
            <> map (uncurry genPred) (zip [minBound .. maxBound] [1, 1, 2, 2])
            <> [ KJNext <$> genSort <*> genKorePattern
               , KJRewrites <$> genSort <*> genKorePattern <*> genKorePattern
               , KJMultiOr <$> Gen.element [Left, Right] <*> genSort <*> upTo 12 genKorePattern
               , KJMultiApp <$> Gen.element [Left, Right] <*> genId (Just '\\') <*> exactly 3 genSort <*> upTo 12 genKorePattern
               ]
  where
    genApp :: Gen KorePattern
    genApp = do
        sorts <- upTo 10 genSort
        args <- exactly (length sorts) genKorePattern
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
    Gen.choice
        [ SortVariable <$> genVarName
        , Sort <$> genId Nothing <*> upTo 10 genSort
        ]

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

showExamples :: IO a
showExamples =
    forever $ do
        korePattern <- Gen.sample genKorePattern
        BS.putStr $ encodeKoreJson korePattern
        void getLine
