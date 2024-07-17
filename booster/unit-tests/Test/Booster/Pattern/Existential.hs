{-# LANGUAGE QuasiQuotes #-}

module Test.Booster.Pattern.Existential (
    test_matchExistential,
    test_instantiateExistentials,
    test_instantiateExistentialsMany,
    test_applyExSimplification,
) where

import Control.Monad.Logger (runNoLoggingT, runStderrLoggingT)
import Control.Monad.Trans.Reader (runReaderT)
import Data.Coerce (coerce)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Proxy (Proxy (..))
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import GHC.IO.Unsafe (unsafePerformIO)
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Log
import Booster.Pattern.ApplyEquations (Direction (..), evaluateTerm)
import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Existential
import Booster.Pattern.Index (CellIndex (..), TermIndex (..))
import Booster.Pattern.Pretty
import Booster.Pattern.Util (markAsExVar, modifyVarName, modifyVariablesInT)
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)
import Booster.Util (Flag (..), withFastLogger)
import Test.Booster.Fixture hiding (inj, var)

test_matchExistential :: TestTree
test_matchExistential =
    testGroup
        "matchExistential"
        [ testGroup
            "positive cases -- non-empty substitution"
            [ test
                "One existential -- one binding, left"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "B"))
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                ( Map.fromList [(var "Ex#A", varTerm "C")]
                )
            , test
                "One existential -- one binding, right"
                (Predicate $ LtInt (varTerm "A") (varTerm "Ex#B"))
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                ( Map.fromList [(var "Ex#B", varTerm "D")]
                )
            , test
                "Two existentials -- two bindings"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                ( Map.fromList [(var "Ex#A", varTerm "C"), (var "Ex#B", varTerm "D")]
                )
            ]
        , testGroup
            "negative cases -- empty substitution"
            [ test
                "No existentials"
                (Predicate $ LtInt (varTerm "A") (varTerm "B"))
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                (Map.empty)
            , test
                "Different symbols"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                (Predicate $ EqualsInt (varTerm "C") (varTerm "D"))
                (Map.empty)
            , test
                "Malformed target -- not a symbol application"
                (Predicate $ varTerm "A")
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                (Map.empty)
            , test
                "Malformed known -- not a symbol application"
                (Predicate $ LtInt (varTerm "Ex#C") (varTerm "D"))
                (Predicate $ varTerm "A")
                (Map.empty)
            ]
        ]
  where
    test :: String -> Predicate -> Predicate -> Map Variable Term -> TestTree
    test name target known expected =
        testCase name $
            matchExistential target known
                @?= expected

test_instantiateExistentials :: TestTree
test_instantiateExistentials =
    testGroup
        "instantiateExistentials"
        [ testGroup
            "positive cases -- changed predicate"
            [ test
                "Earlier bindings are preferred"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                [ Predicate $ LtInt (varTerm "C1") (varTerm "D1")
                , Predicate $ LtInt (varTerm "C2") (varTerm "D2")
                ]
                (Predicate $ LtInt (varTerm "C1") (varTerm "D1"))
            , test
                "Can ignore non-matching known"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                [ Predicate $ EqualsInt (varTerm "C1") (varTerm "D1")
                , Predicate $ LtInt (varTerm "C2") (varTerm "D2")
                ]
                (Predicate $ LtInt (varTerm "C2") (varTerm "D2"))
            ]
        , testGroup
            "negative cases -- same predicate"
            [ test
                "No matching known"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                [ Predicate $ EqualsInt (varTerm "C1") (varTerm "D1")
                , Predicate $ EqualsInt (varTerm "C2") (varTerm "D2")
                ]
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
            , test
                "No existentials"
                (Predicate $ LtInt (varTerm "A") (varTerm "B"))
                [ Predicate $ EqualsInt (varTerm "C1") (varTerm "D1")
                , Predicate $ EqualsInt (varTerm "C2") (varTerm "D2")
                ]
                (Predicate $ LtInt (varTerm "A") (varTerm "B"))
            ]
        ]
  where
    test :: String -> Predicate -> [Predicate] -> Predicate -> TestTree
    test name target known expected =
        testCase name $
            let (actual, _subst) = instantiateExistentials (Set.fromList known) target
             in actual @?= expected

test_instantiateExistentialsMany :: TestTree
test_instantiateExistentialsMany =
    testGroup
        "instantiateExistentialsMany"
        [ testGroup
            "positive cases -- changed predicate"
            [ test
                "Earlier bindings are preferred, learned occurrences in consecrative predicates are substituted"
                [Predicate $ LtInt (varTerm "A") (varTerm "Ex#B"), Predicate $ LtInt (varTerm "Ex#B") (varTerm "C")]
                [ Predicate $ LtInt (varTerm "A") (varTerm "D")
                ]
                [Predicate $ LtInt (varTerm "A") (varTerm "D"), Predicate $ LtInt (varTerm "D") (varTerm "C")]
            ]
        ]
  where
    test :: String -> [Predicate] -> [Predicate] -> [Predicate] -> TestTree
    test name targets known expected =
        testCase name $
            let actual = instantiateExistentialsMany (Set.fromList known) targets
             in actual @?= expected

{-# NOINLINE test_applyExSimplification #-}
test_applyExSimplification :: TestTree
test_applyExSimplification =
    testGroup
        "Applying an existential simplification"
        [ testCase "No known predicates, no simplification" $ do
            simpl
                BottomUp
                [trm| rel1{}(ConfX:SomeSort{}, ConfZ:SomeSort{}) |]
                []
                @?= Right [trm| rel1{}(ConfX:SomeSort{}, ConfZ:SomeSort{}) |]
        , testCase
            "Known predicate instantiates the conjuncts, but we don't have reflexivity of rel2, simplification is not applied"
            $ do
                simpl
                    BottomUp
                    [trm| rel1{}(ConfX:SomeSort{}, ConfY:SomeSort{}) |]
                    [ Predicate [trm| rel2{}(ConfX:SomeSort{}, ConfY:SomeSort{}) |]
                    ]
                    @?= Right [trm| rel1{}(ConfX:SomeSort{}, ConfY:SomeSort{}) |]
        , testCase
            "Known predicate instantiates the conjuncts, simplification is not applied, using the extra known condition"
            $ do
                simpl
                    BottomUp
                    [trm| rel1{}(ConfX:SomeSort{}, ConfY:SomeSort{}) |]
                    [ Predicate [trm| rel2{}(ConfX:SomeSort{}, ConfY:SomeSort{}) |]
                    , Predicate [trm| rel2{}(ConfX:SomeSort{}, ConfX:SomeSort{}) |]
                    ]
                    @?= Right [trm| rel3{}(ConfX:SomeSort{}, ConfY:SomeSort{}) |]
        ]
  where
    -- FIXME this function logs to stderr. I find it useful to be able to see the logs when debugging unit tests, but we likely need to make it opt-in.
    simpl direction x knownPredicates = unsafePerformIO $
        withFastLogger Nothing Nothing $ \stderrLogger _ ->
            flip runReaderT (textLogger stderrLogger, ModifiersRep @'[] Proxy) $
                unLoggerT $
                    (fst <$>) $
                        evaluateTerm direction exSimplDef Nothing Nothing (Set.fromList knownPredicates) x

----------------------------------------

var :: VarName -> Variable
var variableName = Variable{variableSort = someSort, variableName}

varTerm :: VarName -> Term
varTerm variableName = Var $ Variable{variableSort = someSort, variableName}

----------------------------------------

{- | This is a hacky helper to construct an equation with existentials in the requires clause.
  The requires clause is traversed and the the variables given in @exVarNames@ are prefixed with Ex#.
  TODO: refactor once we do not need to bypass the internalisation checks.
-}
equationExRequires ::
    Maybe Text -> Term -> Term -> [Predicate] -> [VarName] -> Priority -> RewriteRule t
equationExRequires ruleLabel lhs rhs requires exVarNames priority =
    RewriteRule
        { lhs = lhs
        , rhs = rhs
        , requires =
            Set.fromList $
                map
                    ( coerce
                        . modifyVariablesInT
                            (modifyVarName (\name -> if name `elem` exVarNames then markAsExVar name else name))
                        . coerce
                    )
                    requires
        , ensures = mempty
        , attributes =
            AxiomAttributes
                { location = Nothing
                , priority
                , ruleLabel
                , simplification = Flag True
                , preserving = Flag False
                , concreteness = Unconstrained
                , uniqueId = maybe mockUniqueId UniqueId ruleLabel
                , smtLemma = Flag False
                }
        , computedAttributes = ComputedAxiomAttributes False []
        , existentials = mempty -- intentionally left blank to bypass the checks in ApplyEquations.hs
        }

exSimplDef :: KoreDefinition
exSimplDef =
    defWithSymbols
        { simplifications =
            mkTheory
                [
                    ( index "rel1"
                    ,
                        [ equationExRequires -- rel1(X, Y) => rel3(X, Y) requires [rel2(X,?C), rel2(?C,Y)]
                            (Just "rel1-rel3-ex")
                            [trm| rel1{}(EqX:SomeSort{}, EqY:SomeSort{}) |]
                            [trm| rel3{}(EqX:SomeSort{}, EqY:SomeSort{}) |]
                            ( [ Predicate [trm| rel2{}(EqX:SomeSort{}, EqC:SomeSort{}) |]
                              , Predicate [trm| rel2{}(EqC:SomeSort{}, EqY:SomeSort{}) |]
                              ]
                            )
                            ["EqC"]
                            50
                        ]
                    )
                ]
        }
  where
    defWithSymbols =
        testDefinition
            { symbols =
                testDefinition.symbols
                    <> Map.fromList
                        [("rel1", rel1)]
            }

rel1, rel2, rel3 :: Symbol
rel1 = [symb| symbol rel1{}(SomeSort{}, SomeSort{}) : SomeSort{} [function{}(), total{}()] |]
rel2 = [symb| symbol rel2{}(SomeSort{}, SomeSort{}) : SomeSort{} [function{}(), total{}()] |]
rel3 = [symb| symbol rel3{}(SomeSort{}, SomeSort{}) : SomeSort{} [function{}(), total{}()] |]

mkTheory :: [(TermIndex, [RewriteRule t])] -> Theory (RewriteRule t)
mkTheory = Map.map mkPriorityGroups . Map.fromList
  where
    mkPriorityGroups :: [RewriteRule t] -> Map Priority [RewriteRule t]
    mkPriorityGroups rules =
        Map.unionsWith
            (<>)
            [Map.fromList [(r.attributes.priority, [r])] | r <- rules]

index :: SymbolName -> TermIndex
index = TermIndex . (: []) . TopSymbol
