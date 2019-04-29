module Test.Kore.Step.Simplification.Not
    ( test_simplifyEvaluated
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map.Strict as Map

import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Valid
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Pattern )
import qualified Kore.Step.Pattern as Pattern
import qualified Kore.Step.Predicate as Predicate
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.Not as Not
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import           Kore.Syntax.Variable
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import qualified SMT

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import qualified Test.Kore.Step.MockSimplifiers as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_simplifyEvaluated :: [TestTree]
test_simplifyEvaluated =
    [ [Pattern.top] `becomes_` []
    , [] `becomes_` [Pattern.top]
    , [termX] `becomes_` [mkNot <$> termX]
    , [equalsXA] `becomes_` [notEqualsXA]
    , [substXA] `becomes_` [notEqualsXA]
    , [equalsXA, equalsXB] `becomes_` [neitherXAB]
    ]
  where
    becomes_ original expected =
        testCase "becomes" $ do
            actual <- simplifyEvaluated (OrPattern.fromPatterns original)
            assertEqualWithExplanation "" (OrPattern.fromPatterns expected) actual

termX :: Pattern Object Variable
termX = Pattern.fromTermLike (mkVar Mock.x)

equalsXA :: Pattern Object Variable
equalsXA = fromPredicate equalsXA_

equalsXB :: Pattern Object Variable
equalsXB = fromPredicate equalsXB_

equalsXA_ :: Syntax.Predicate Variable
equalsXA_ = Syntax.Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.a

equalsXB_ :: Syntax.Predicate Variable
equalsXB_ = Syntax.Predicate.makeEqualsPredicate (mkVar Mock.x) Mock.b

notEqualsXA :: Pattern Object Variable
notEqualsXA = fromPredicate $ Syntax.Predicate.makeNotPredicate equalsXA_

neitherXAB :: Pattern Object Variable
neitherXAB =
    fromPredicate
    $ Syntax.Predicate.makeAndPredicate
        (Syntax.Predicate.makeNotPredicate equalsXA_)
        (Syntax.Predicate.makeNotPredicate equalsXB_)

substXA :: Pattern Object Variable
substXA = fromSubstitution $ Substitution.unsafeWrap [(Mock.x, Mock.a)]

fromPredicate :: Syntax.Predicate Variable -> Pattern Object Variable
fromPredicate =
    Pattern.fromPredicate
    . Predicate.fromPredicate

fromSubstitution
    :: Substitution Variable
    -> Pattern Object Variable
fromSubstitution =
    Pattern.fromPredicate
    . Predicate.fromSubstitution

simplifyEvaluated
    :: OrPattern Object Variable
    -> IO (OrPattern Object Variable)
simplifyEvaluated =
    SMT.runSMT SMT.defaultConfig
    . evalSimplifier emptyLogger
    . Not.simplifyEvaluated
        mockMetadataTools
        (Mock.substitutionSimplifier mockMetadataTools)
        (Simplifier.create mockMetadataTools Map.empty)
        Map.empty

mockMetadataTools :: SmtMetadataTools Attribute.Symbol
mockMetadataTools =
    Mock.makeMetadataTools
        Mock.attributesMapping
        Mock.headTypeMapping
        Mock.sortAttributesMapping
        Mock.subsorts
        Mock.headSortsMapping
        Mock.smtDeclarations
