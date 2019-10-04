module Test.Kore.Strategies.OnePath.Verification
    ( test_onePathVerification
    ) where

import Test.Tasty

import Data.Default
    ( def
    )
import Data.Limit
    ( Limit (..)
    )

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Internal.Pattern
    ( Conditional (Conditional)
    )
import Kore.Internal.Pattern as Conditional
    ( Conditional (..)
    )
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeEqualsPredicate
    , makeNotPredicate
    , makeTruePredicate
    )
import Kore.Step.Rule
    ( OnePathRule (..)
    , RewriteRule (..)
    , RulePattern (..)
    )
import Kore.Strategies.Goal

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Strategies.Common
import Test.Tasty.HUnit.Ext

test_onePathVerification :: [TestTree]
test_onePathVerification =
    [ testCase "Runs zero steps" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error a
        actual <- runVerification
            (Limit 0)
            [simpleAxiom Mock.a Mock.b]
            [simpleClaim Mock.a Mock.b]
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.a)
            actual
    , testCase "Runs one step" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: error b
        -- Note that the check that we have reached the destination happens
        -- at the beginning of each step. At the beginning of the first step
        -- the pattern is 'a', so we didn't reach our destination yet, even if
        -- the rewrite transforms 'a' into 'b'. We detect the success at the
        -- beginning of the second step, which does not run here.
        actual <- runVerification
            (Limit 1)
            [simpleAxiom Mock.a Mock.b]
            [simpleClaim Mock.a Mock.b]
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.b)
            actual
    , testCase "Returns first failing claim" $ do
        -- Axiom: a => b or c
        -- Claim: a => d
        -- Expected: error b
        actual <- runVerification
            (Limit 1)
            [simpleAxiom Mock.a (mkOr Mock.b Mock.c)]
            [simpleClaim Mock.a Mock.d]
        assertEqual ""
            (Left . Pattern.fromTermLike $ Mock.b)
            actual
    , testCase "Verifies one claim" $ do
        -- Axiom: a => b
        -- Claim: a => b
        -- Expected: success
        actual <- runVerification
            (Limit 2)
            [simpleAxiom Mock.a Mock.b]
            [simpleClaim Mock.a Mock.b]
        assertEqual ""
            (Right ())
            actual
    , testCase "Trusted claim cannot prove itself" $ do
        -- Trusted Claim: a => b
        -- Expected: error a
        actual <- runVerification
            (Limit 4)
            []
            [ simpleTrustedClaim Mock.a Mock.b
            , simpleClaim Mock.a Mock.b
            ]
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.a)
            actual
    , testCase "Verifies one claim multiple steps" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Claim: a => c
        -- Expected: success
        actual <- runVerification
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            ]
            [simpleClaim Mock.a Mock.c]
        assertEqual ""
            (Right ())
            actual
    , testCase "Verifies one claim stops early" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Claim: a => b
        -- Expected: success
        actual <- runVerification
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            ]
            [simpleClaim Mock.a Mock.c]
        assertEqual ""
            (Right ())
            actual
    , testCase "Verifies one claim with branching" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr11(x) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: success
        actual <- runVerification
            (Limit 4)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom (Mock.functionalConstr11 (mkElemVar Mock.x)) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [simpleClaim (Mock.functionalConstr10 (mkElemVar Mock.x)) Mock.b]
        assertEqual "" (Right ()) actual
    , testCase "Partial verification failure" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: error constr11(x) and x != a
        actual <- runVerification
            (Limit 3)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [simpleClaim (Mock.functionalConstr10 (mkElemVar Mock.x)) Mock.b]
        assertEqual ""
            (Left Conditional
                { term = Mock.functionalConstr11 (mkElemVar Mock.x)
                , predicate =
                    makeNotPredicate $ makeEqualsPredicate (mkElemVar Mock.x) Mock.a
                , substitution = mempty
                }
            )
            actual
    , testCase "Verifies two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => c
        -- Claim: d => e
        -- Expected: success
        actual <- runVerification
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleClaim Mock.a Mock.c
            , simpleClaim Mock.d Mock.e
            ]
        assertEqual ""
            (Right ())
            actual
    , testCase "fails first of two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => e
        -- Claim: d => e
        -- Expected: error c
        actual <- runVerification
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleClaim Mock.a Mock.e
            , simpleClaim Mock.d Mock.e
            ]
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.c)
            actual
    , testCase "fails second of two claims" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: d => e
        -- Claim: a => c
        -- Claim: d => c
        -- Expected: error e
        actual <- runVerification
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleClaim Mock.a Mock.c
            , simpleClaim Mock.d Mock.c
            ]
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.e)
            actual
    , testCase "second proves first but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => c
        -- Expected: error b
        actual <- runVerification
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleClaim Mock.a Mock.d
            , simpleClaim Mock.b Mock.c
            ]
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.b)
            actual
    , testCase "first proves second but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: error b
        actual <- runVerification
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleClaim Mock.b Mock.c
            , simpleClaim Mock.a Mock.d
            ]
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.b)
            actual
    , testCase "trusted second proves first" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Trusted Claim: b => c
        -- Expected: success
        actual <- runVerification
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleClaim Mock.a Mock.d
            , simpleTrustedClaim Mock.b Mock.c
            ]
        assertEqual ""
            (Right ())
            actual
    , testCase "trusted first proves second" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: success
        actual <- runVerification
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleTrustedClaim Mock.b Mock.c
            , simpleClaim Mock.a Mock.d
            ]
        assertEqual ""
            (Right ())
            actual
    , testCase "Prefers using claims for rewriting" $ do
        -- Axiom: a => b
        -- Axiom: b => c
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => e
        -- Expected: error e
        --    first verification: a=>b=>e,
        --        without second claim would be: a=>b=>c=>d
        --    second verification: b=>c=>d, not visible here
        actual <- runVerification
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleClaim Mock.a Mock.d
            , simpleClaim Mock.b Mock.e
            ]
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.e)
            actual
    , testCase "Provable using one-path; not provable using all-path" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claim: a => b
        -- Expected: success
        actual <- runVerification
            (Limit 5)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleClaim Mock.a Mock.b ]
        assertEqual ""
            (Right ())
            actual
    ]

simpleAxiom
    :: TermLike Variable
    -> TermLike Variable
    -> Rule (OnePathRule Variable)
simpleAxiom left right =
    OnePathRewriteRule $ simpleRewrite left right

simpleClaim
    :: TermLike Variable
    -> TermLike Variable
    -> OnePathRule Variable
simpleClaim left right =
    OnePathRule . getRewriteRule $ simpleRewrite left right

simpleTrustedClaim
    :: TermLike Variable
    -> TermLike Variable
    -> OnePathRule Variable
simpleTrustedClaim left right =
    OnePathRule
    $ RulePattern
            { left = left
            , antiLeft = Nothing
            , right = right
            , requires = makeTruePredicate
            , ensures = makeTruePredicate
            , attributes = def
                { Attribute.trusted = Attribute.Trusted True }
            }
