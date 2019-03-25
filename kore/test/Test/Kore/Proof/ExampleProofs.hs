module Test.Kore.Proof.ExampleProofs (test_exampleProofs) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( Assertion, assertEqual, testCase )

import Data.Text.Prettyprint.Doc

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.Proof.FunctionalityAxioms
import Kore.Proof.LineBasedProof
import Kore.Proof.Proof
import Kore.Proof.Unification

test_exampleProofs :: TestTree
test_exampleProofs = testGroup "exampleProofs" $
    [ testCase "unify f(f(c,d),e) = f(a,b)" $ assertNF unifyffabcfde
    , testCase "f(f(a,b),f(c,d)) is functional" $ assertNF ffabfcdIsFunctional
    ]

-- | Since Tasty doesn't seem to include an actual predicate that says
-- "This evaluates to normal form without throwing an error"
-- I just did this instead. And why not convert it to a line-based-proof
-- to test that functionality too.
assertNF :: Proof -> Assertion
assertNF x = let y = show $ pretty $ toLineProof x in assertEqual "" y y

s :: Sort Object
s = mkSort "*"

f :: SymbolOrAlias Object
f = symS "f" [s, s]

a, b, c, d, e :: Variable Object
[a, b, c, d, e] = map (`varS` s) ["a","b","c","d","e"]

lhs :: Term
lhs = mkApp s f [mkApp s f [mkVar a, mkVar b], mkVar c]

rhs :: Term
rhs = mkApp s f [mkVar d, mkVar e]

unifyffabcfde :: Proof
Right unifyffabcfde = unificationProof lhs rhs

ffabfcdIsFunctional :: Proof
ffabfcdIsFunctional = proveFunctional $
    mkApp s f [mkApp s f [mkVar a, mkVar b], mkApp s f [mkVar c, mkVar d]]
