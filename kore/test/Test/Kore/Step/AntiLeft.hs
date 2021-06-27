module Test.Kore.Step.AntiLeft (
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
import Kore.Step.AntiLeft
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
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

newtype AntiLeftTerm = AntiLeftTerm {_getAntileftTerm :: TermLike VariableName}

test_antiLeft :: [TestTree]
test_antiLeft =
    [ testCase "Simple antiLeft" $ do
        let expect = makeCeilPredicate (mkAnd Mock.cf Mock.a)
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( mkOr
                            ( applyAliasToNoArgs
                                "B"
                                (mkAnd (mkTop Mock.testSort) Mock.a)
                            )
                            (mkBottom Mock.testSort)
                        )
                    )
                )
                Mock.cf
        assertEqual "" expect actual
    , testCase "AntiLeft with requires" $ do
        let expect =
                makeAndPredicate
                    (makeCeilPredicate Mock.cg)
                    (makeCeilPredicate (mkAnd Mock.cf Mock.a))
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( mkOr
                            ( applyAliasToNoArgs
                                "B"
                                (mkAnd (mkCeil Mock.testSort Mock.cg) Mock.a)
                            )
                            (mkBottom Mock.testSort)
                        )
                    )
                )
                Mock.cf
        assertEqual "" expect actual
    , testCase "AntiLeft multiple rules" $ do
        let expect =
                makeOrPredicate
                    (makeCeilPredicate (mkAnd Mock.cf Mock.a))
                    (makeCeilPredicate (mkAnd Mock.cf Mock.b))
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( mkOr
                            ( applyAliasToNoArgs
                                "B"
                                (mkAnd (mkTop Mock.testSort) Mock.a)
                            )
                            ( mkOr
                                ( applyAliasToNoArgs
                                    "C"
                                    (mkAnd (mkTop Mock.testSort) Mock.b)
                                )
                                (mkBottom Mock.testSort)
                            )
                        )
                    )
                )
                Mock.cf
        assertEqual "" expect actual
    , testCase "Recursive antiLeft" $ do
        let expect =
                makeOrPredicate
                    (makeCeilPredicate (mkAnd Mock.cf Mock.a))
                    (makeCeilPredicate (mkAnd Mock.cf Mock.b))
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( mkOr
                            ( applyAliasToNoArgs
                                "B"
                                ( mkOr
                                    ( applyAliasToNoArgs
                                        "C"
                                        (mkAnd (mkTop Mock.testSort) Mock.a)
                                    )
                                    (mkBottom Mock.testSort)
                                )
                            )
                            ( mkOr
                                ( applyAliasToNoArgs
                                    "D"
                                    (mkAnd (mkTop Mock.testSort) Mock.b)
                                )
                                (mkBottom Mock.testSort)
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
                        ( mkAnd
                            (Mock.g (mkElemVar Mock.x))
                            (Mock.f (mkElemVar Mock.var_x_0))
                        )
                    )
        actual <-
            parseAndApply
                ( AntiLeftTerm
                    ( applyAliasToNoArgs
                        "A"
                        ( mkOr
                            ( mkExists
                                Mock.x
                                ( applyAliasToNoArgs
                                    "B"
                                    ( mkAnd
                                        (mkTop Mock.testSort)
                                        (Mock.f (mkElemVar Mock.x))
                                    )
                                )
                            )
                            (mkBottom Mock.testSort)
                        )
                    )
                )
                (Mock.g (mkElemVar Mock.x))
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
    Text -> TermLike VariableName -> TermLike VariableName
applyAliasToNoArgs name right =
    mkApplyAlias
        Alias
            { aliasConstructor = testId name
            , aliasParams = []
            , aliasSorts = applicationSorts [] Mock.testSort
            , aliasLeft = []
            , aliasRight = right
            }
        []
