module Test.Kore.Proof.ExampleProofs (test_exampleProofs) where

import           Test.Tasty                           (TestTree, testGroup)
import           Test.Tasty.HUnit                     (Assertion, assertEqual,
                                                       testCase)

import           Kore.AST.Common
import           Kore.AST.MetaOrObject

import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns

import           Kore.Proof.FunctionalityAxioms
import           Kore.Proof.Proof
import           Kore.Proof.Dummy

import           Kore.Proof.Unification
import           Kore.Proof.LineBasedProof

import           Data.Text.Prettyprint.Doc

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
lhs = dummyEnvironment $ mkApp f [mkApp f [V a, V b], V c]

rhs :: Term
rhs = dummyEnvironment $ mkApp f [V d, V e]

unifyffabcfde :: Proof
Right unifyffabcfde = dummyEnvironment $ unificationProof lhs rhs

ffabfcdIsFunctional :: Proof
ffabfcdIsFunctional = dummyEnvironment $ proveFunctional $
    mkApp f [mkApp f [V a, V b], mkApp f [V c, V d]]

