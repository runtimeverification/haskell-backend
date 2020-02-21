module Test.Kore.Strategies.AllPath.Verification
    ( test_allPathVerification
    ) where

import Prelude.Kore

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
import Kore.Internal.Predicate
    ( makeEqualsPredicate
    , makeNotPredicate
    , makeTruePredicate_
    )
import Kore.Internal.TermLike
import Kore.Step.RulePattern
    ( AllPathRule (..)
    , RulePattern (..)
    , injectTermIntoRHS
    )
import Kore.Strategies.Goal

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Strategies.Common
import Test.Tasty.HUnit.Ext

test_allPathVerification :: [TestTree]
test_allPathVerification =
    [ testCase "Identity spec" $ do
        -- Axioms: []
        -- Claims: a => a
        -- Expected: success
        actual <- runVerificationToPattern
            Unlimited
            (Limit 1)
            []
            [ simpleClaim Mock.a Mock.a ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "Distinct spec" $ do
        -- Axioms: []
        -- Claims: a => b
        -- Expected: error a
        actual <- runVerificationToPattern
            Unlimited
            (Limit 1)
            []
            [ simpleClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.a)
            actual
    -- TODO(Ana): this should be uncommented if we decide
    --            that the destination doesn't need to be
    --            function-like
    -- , testCase "b or c spec" $ do
    --     -- Axioms: a => b
    --     -- Claims: a => b #Or c
    --     -- Expected: success
    --     actual <- runVerificationToPattern
    --         (Limit 2)
    --         Unlimited
    --         [ simpleAxiom Mock.a Mock.b ]
    --         [ simpleClaim Mock.a (mkOr Mock.b Mock.c) ]
    --         []
    --     assertEqual ""
    --         (Right ())
    --         actual
    , testCase "Everything is provable when we have cyclic rules" $ do
        -- Axioms: a => a
        -- Claims: a => b
        -- Expected: success
        actual <- runVerificationToPattern
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.a ]
            [ simpleClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Right ())
            actual
    -- TODO(Ana): this should be uncommented if we decide
    --            that the destination doesn't need to be
    --            function-like
    -- , testCase "Concurrent rules" $ do
    --     -- Axioms:
    --     --     a => b
    --     --     a => c
    --     -- Claims: a => b #Or c
    --     -- Expected: success
    --     actual <- runVerificationToPattern
    --         Unlimited
    --         (Limit 2)
    --         [ simpleAxiom Mock.a Mock.b
    --         , simpleAxiom Mock.a Mock.c
    --         ]
    --         [ simpleClaim Mock.a (mkOr Mock.b Mock.c) ]
    --         []
    --     assertEqual ""
    --         (Right ())
    --         actual
    , testCase "Provable using one-path; not provable using all-path" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claim: a => b
        -- Expected: error c
        actual <- runVerificationToPattern
            Unlimited
            (Limit 2)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleClaim Mock.a Mock.b ]
            []
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.c)
            actual
    , testCase "Verifies one claim with branching" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr11(x) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: success
        actual <- runVerificationToPattern
            Unlimited
            (Limit 4)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom (Mock.functionalConstr11 (mkElemVar Mock.x)) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [simpleClaim (Mock.functionalConstr10 (mkElemVar Mock.x)) Mock.b]
            []
        assertEqual "" (Right ()) actual
    , testCase "Partial verification failure" $ do
        -- Axiom: constr11(a) => b
        -- Axiom: constr10(x) => constr11(x)
        -- Claim: constr10(x) => b
        -- Expected: error constr11(x) and x != a
        actual <- runVerificationToPattern
            Unlimited
            (Limit 3)
            [ simpleAxiom (Mock.functionalConstr11 Mock.a) Mock.b
            , simpleAxiom
                (Mock.functionalConstr10 (mkElemVar Mock.x))
                (Mock.functionalConstr11 (mkElemVar Mock.x))
            ]
            [simpleClaim (Mock.functionalConstr10 (mkElemVar Mock.x)) Mock.b]
            []
        assertEqual ""
            (Left Conditional
                { term = Mock.functionalConstr11 (mkElemVar Mock.x)
                , predicate =
                    makeNotPredicate
                        (makeEqualsPredicate Mock.testSort
                            (mkElemVar Mock.x)
                            Mock.a
                        )
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
        actual <- runVerificationToPattern
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleClaim Mock.a Mock.c
            , simpleClaim Mock.d Mock.e
            ]
            []
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
        actual <- runVerificationToPattern
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleClaim Mock.a Mock.e
            , simpleClaim Mock.d Mock.e
            ]
            []
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
        actual <- runVerificationToPattern
            Unlimited
            (Limit 3)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.d Mock.e
            ]
            [ simpleClaim Mock.a Mock.c
            , simpleClaim Mock.d Mock.c
            ]
            []
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.e)
            actual
    , testCase "second proves first but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: a => d
        -- Claim: b => c
        -- Expected: error b
        actual <- runVerificationToPattern
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleClaim Mock.a Mock.d
            , simpleClaim Mock.b Mock.c
            ]
            []
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.b)
            actual
    , testCase "first proves second but fails" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: error b
        actual <- runVerificationToPattern
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleClaim Mock.b Mock.c
            , simpleClaim Mock.a Mock.d
            ]
            []
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.b)
            actual
    , testCase "trusted first proves second" $ do
        -- Axiom: a => b
        -- Axiom: c => d
        -- Claim: b => c
        -- Claim: a => d
        -- Expected: success
        actual <- runVerificationToPattern
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleTrustedClaim Mock.b Mock.c
            , simpleClaim Mock.a Mock.d
            ]
            []
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
        actual <- runVerificationToPattern
            Unlimited
            (Limit 4)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.b Mock.c
            , simpleAxiom Mock.c Mock.d
            ]
            [ simpleClaim Mock.a Mock.d
            , simpleClaim Mock.b Mock.e
            ]
            []
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.e)
            actual
    , testCase "TESTING Priority: should apply first trusted claim" $ do
        -- Axioms:
        --     a => b
        -- Claims: a => d
        --        b => c [trusted]
        --        b => d [trusted]
        -- Expected: error c
        actual <- runVerificationToPattern
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b ]
            [ simpleClaim Mock.a Mock.d
            , simpleTrustedClaim Mock.b Mock.c
            , simpleTrustedClaim Mock.b Mock.d
            ]
            []
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.c)
            actual
    , testCase "TESTING Priority: should apply trusted\
               \ claim with higher priority" $ do
        -- Axioms:
        --     a => b
        -- Claims: a => d
        --        b => c [trusted, priority(2)]
        --        b => d [trusted, priority(1)]
        -- Expected: success
        actual <- runVerificationToPattern
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b ]
            [ simpleClaim Mock.a Mock.d
            , simpleTrustedPriorityClaim Mock.b Mock.c 2
            , simpleTrustedPriorityClaim Mock.b Mock.d 1
            ]
            []
        assertEqual ""
            (Right ())
            actual
    , testCase "TESTING Priority: should apply trusted\
               \ claim with higher priority" $ do
        -- Axioms:
        --     a => b
        -- Claims: a => d
        --        b => c [trusted, priority(2)]
        --        b => d [trusted, priority(1)]
        -- Expected: error c
        actual <- runVerificationToPattern
            Unlimited
            Unlimited
            [ simpleAxiom Mock.a Mock.b ]
            [ simpleClaim Mock.a Mock.d
            , simpleTrustedPriorityClaim Mock.b Mock.d 2
            , simpleTrustedPriorityClaim Mock.b Mock.c 1
            ]
            []
        assertEqual ""
            (Left $ Pattern.fromTermLike Mock.c)
            actual
    ]

simpleAxiom
    :: TermLike Variable
    -> TermLike Variable
    -> Rule (AllPathRule Variable)
simpleAxiom left right =
    AllPathRewriteRule $ simpleRewrite left right

simpleClaim
    :: TermLike Variable
    -> TermLike Variable
    -> AllPathRule Variable
simpleClaim left right =
    AllPathRule
    RulePattern
        { left = left
        , antiLeft = Nothing
        , requires = makeTruePredicate_
        , rhs = injectTermIntoRHS right
        , attributes = def
        }

simpleTrustedClaim
    :: TermLike Variable
    -> TermLike Variable
    -> AllPathRule Variable
simpleTrustedClaim left right =
    AllPathRule
    RulePattern
        { left = left
        , antiLeft = Nothing
        , requires = makeTruePredicate_
        , rhs = injectTermIntoRHS right
        , attributes = def
            { Attribute.trusted = Attribute.Trusted True }
        }

simpleTrustedPriorityClaim
    :: TermLike Variable
    -> TermLike Variable
    -> Integer
    -> AllPathRule Variable
simpleTrustedPriorityClaim left right priority =
    AllPathRule
    RulePattern
        { left = left
        , antiLeft = Nothing
        , requires = makeTruePredicate_
        , rhs = injectTermIntoRHS right
        , attributes = def
            { Attribute.trusted = Attribute.Trusted True
            , Attribute.priority = Attribute.Priority (Just priority)
            }
        }
