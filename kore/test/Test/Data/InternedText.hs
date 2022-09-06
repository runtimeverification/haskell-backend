module Test.Data.InternedText (
    hprop_hashes_id,
    hprop_tests_equality_using_id,
    hprop_internText_does_not_change_the_strings_contents,
    hprop_internText_returns_the_same_id_for_the_same_string,
    hprop_internText_returns_different_ids_for_different_strings,
) where

import Data.InternedText
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude.Kore

hprop_hashes_id :: Property
hprop_hashes_id =
    property $ do
        text <- forAll $ Gen.text (Range.linear 0 10) Gen.unicode
        iden <- forAll $ Gen.word Range.linearBounded
        salt <- forAll $ Gen.int Range.linearBounded

        let interned = UnsafeMkInternedText text iden

        hash iden === hash interned
        hashWithSalt salt iden === hashWithSalt salt interned

hprop_tests_equality_using_id :: Property
hprop_tests_equality_using_id =
    property $ do
        text1 <- forAll $ Gen.text (Range.linear 0 10) Gen.unicode
        text2 <- forAll $ Gen.text (Range.linear 0 10) Gen.unicode

        -- Generate two different IDs
        iden1 <- forAll $ Gen.word Range.linearBounded
        iden2 <- forAll $ Gen.word $ Range.linear (iden1 + 1) maxBound

        -- When the two IDs are different, then the two `InternedText`s are different
        -- (regardless of the strings' contents).
        UnsafeMkInternedText text1 iden1 /== UnsafeMkInternedText text2 iden2

        -- When the two IDs are equal, then the two `InternedText`s are equal
        -- (regardless of the strings' contents).
        UnsafeMkInternedText text1 iden1 === UnsafeMkInternedText text2 iden1

hprop_internText_does_not_change_the_strings_contents :: Property
hprop_internText_does_not_change_the_strings_contents =
    property $ do
        text <- forAll $ Gen.text (Range.linear 0 10) Gen.unicode
        internedText (internText text) === text

hprop_internText_returns_the_same_id_for_the_same_string :: Property
hprop_internText_returns_the_same_id_for_the_same_string =
    property $ do
        text <- forAll $ Gen.text (Range.linear 0 10) Gen.unicode

        internedId (internText text) === internedId (internText text)

hprop_internText_returns_different_ids_for_different_strings :: Property
hprop_internText_returns_different_ids_for_different_strings =
    property $ do
        text1 <- forAll $ Gen.text (Range.linear 0 10) Gen.unicode
        text2 <- forAll $ Gen.filter (/= text1) $ Gen.text (Range.linear 1 10) Gen.unicode

        internedId (internText text1) /== internedId (internText text2)
