module Test.Kore.Rewrite.AntiLeft (
    test_antiLeft,
) where

import Data.Text (
    Text,
 )
import Kore.Internal.Alias (
    Alias (Alias),
 )
import qualified Kore.Internal.Alias as Alias.DoNotUse
import Kore.Internal.ApplicationSorts (
    applicationSorts,
 )
import Kore.Internal.Predicate (
    Predicate,
    makeAndPredicate,
    makeCeilPredicate,
    makeExistsPredicate,
    makeOrPredicate,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.TermLike (
    mkAnd,
    mkApplyAlias,
    mkBottom,
    mkCeil,
    mkElemVar,
    mkExists,
    mkOr,
    mkTop,
 )
import Kore.Internal.TermLike.TermLike (
    TermLike,
 )
import Kore.Rewrite.AntiLeft
import Kore.Syntax.Variable (
    VariableName,
 )
import Kore.Unparser (
    unparse,
 )
import Prelude.Kore
import qualified Pretty (
    vsep,
 )
import Test.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import qualified Kore.Validate as Validated
import Test.Tasty
import Test.Tasty.HUnit.Ext

newtype AntiLeftTerm = AntiLeftTerm {_getAntileftTerm :: Validated.Pattern VariableName}

test_antiLeft :: [TestTree]
test_antiLeft =
    [ testCase "Simple antiLeft" $ do
        let expect = makeCeilPredicate (TermLike.mkAnd Mock.cf Mock.a)
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( Validated.mkOr
                            ( applyAliasToNoArgs
                                "B"
                                (Validated.mkAnd
                                    (Validated.mkTop Mock.testSort)
                                    (TermLike.fromTermLike Mock.a)
                                )
                            )
                            (Validated.mkBottom Mock.testSort)
                        )
                    )
                )
                Mock.cf
        assertEqual "" expect actual
    , testCase "AntiLeft with requires" $ do
        let expect =
                makeAndPredicate
                    (makeCeilPredicate Mock.cg)
                    (makeCeilPredicate (TermLike.mkAnd Mock.cf Mock.a))
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( Validated.mkOr
                            ( applyAliasToNoArgs
                                "B"
                                (Validated.mkAnd
                                    (Validated.mkCeil Mock.testSort (TermLike.fromTermLike Mock.cg))
                                    (TermLike.fromTermLike Mock.a)
                                )
                            )
                            (Validated.mkBottom Mock.testSort)
                        )
                    )
                )
                Mock.cf
        assertEqual "" expect actual
    , testCase "AntiLeft multiple rules" $ do
        let expect =
                makeOrPredicate
                    (makeCeilPredicate (TermLike.mkAnd Mock.cf Mock.a))
                    (makeCeilPredicate (TermLike.mkAnd Mock.cf Mock.b))
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( Validated.mkOr
                            ( applyAliasToNoArgs
                                "B"
                                (Validated.mkAnd (mkTop Mock.testSort) Mock.a)
                            )
                            ( Validated.mkOr
                                ( applyAliasToNoArgs
                                    "C"
                                    (Validated.mkAnd (mkTop Mock.testSort) Mock.b)
                                )
                                (Validated.mkBottom Mock.testSort)
                            )
                        )
                    )
                )
                Mock.cf
        assertEqual "" expect actual
    , testCase "Recursive antiLeft" $ do
        let expect =
                makeOrPredicate
                    (makeCeilPredicate (TermLike.mkAnd Mock.cf Mock.a))
                    (makeCeilPredicate (TermLike.mkAnd Mock.cf Mock.b))
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( Validated.mkOr
                            ( applyAliasToNoArgs
                                "B"
                                ( Validated.mkOr
                                    ( applyAliasToNoArgs
                                        "C"
                                        (Validated.mkAnd (mkTop Mock.testSort) Mock.a)
                                    )
                                    (Validated.mkBottom Mock.testSort)
                                )
                            )
                            ( Validated.mkOr
                                ( applyAliasToNoArgs
                                    "D"
                                    (Validated.mkAnd (mkTop Mock.testSort) Mock.b)
                                )
                                (Validated.mkBottom Mock.testSort)
                            )
                        )
                    )
                )
                Mock.cf
        assertEqual "" expect actual
    , testCase "Quantified antiLeft" $ do
        let expect =
                makeExistsPredicate
                    Mock.var_x_0
                    ( makeCeilPredicate
                        ( Validated.mkAnd
                            (Mock.g (Validated.mkElemVar Mock.x))
                            (Mock.f (Validated.mkElemVar Mock.var_x_0))
                        )
                    )
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( Validated.mkOr
                            ( Validated.mkExists
                                Mock.x
                                ( applyAliasToNoArgs
                                    "B"
                                    ( Validated.mkAnd
                                        (Validated.mkTop Mock.testSort)
                                        (Mock.f (Validated.mkElemVar Mock.x))
                                    )
                                )
                            )
                            (Validated.mkBottom Mock.testSort)
                        )
                    )
                )
                (Mock.g (Validated.mkElemVar Mock.x))
        assertEqual "" expect actual
    ]

parseAndApply ::
    AntiLeftTerm ->
    TermLike VariableName ->
    IO (Predicate VariableName)
parseAndApply (AntiLeftTerm antiLeftTerm) configurationTerm = do
    antiLeft <- case parse antiLeftTerm of
        Nothing ->
            (assertFailure . show . Pretty.vsep)
                [ "Could not parse antiLeft: "
                , unparse antiLeftTerm
                ]
        Just result -> return result
    return (antiLeftPredicate antiLeft configurationTerm)

applyAliasToNoArgs ::
    Text -> Validated.Pattern VariableName -> Validated.Pattern VariableName
applyAliasToNoArgs name right =
    Validated.mkApplyAlias
        Alias
            { aliasConstructor = testId name
            , aliasParams = []
            , aliasSorts = applicationSorts [] Mock.testSort
            , aliasLeft = []
            , aliasRight = right
            }
        []
