module Test.Kore.Step.SMT.Translate
    ( test_translatePredicateWith
    ) where

import Prelude.Kore hiding
    ( and
    )

import Test.Tasty

import Control.Error
    ( runMaybeT
    )
import qualified Data.Text as Text

import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
import qualified Kore.Step.SMT.Evaluator as Evaluator
import Kore.Step.SMT.Translate
    ( Translator
    , evalTranslator
    )
import SMT
import qualified SMT.SimpleSMT

import Test.Expect
import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.SMT
import Test.Tasty.HUnit.Ext

test_translatePredicateWith :: [TestTree]
test_translatePredicateWith =
    [ testCase "true" $
        translating true `yields` smtTrue
    , testCase "n = n" $
        translating (n `peq` n)
        `yields` (var 0 `eq` var 0)
    , testCase "exists n. true" $
        translating (pexists n true)
        `yields` smtTrue
    , testCase "exists n. n = n" $
        translating (pexists n $ n `peq` n)
        `yields` exists 0 (var 0 `eq` var 0)
    , testCase "exists n. n = m" $
        translating (pexists n $ n `peq` m)
        `yields` exists 0 (var 0 `eq` var 1)
    , testCase "exists x. x = x where x not of a builtin sort" $
        translating (pexists x $ x `peq` x)
        `yields` existst 0 (var 0 `eq` var 0)
    , testCase "n = n and (exists n. n = n)" $
        translating ((n `peq` n) `pand` pexists n (n `peq` n))
        `yields` ((var 0 `eq` var 0) `and` exists 1 (var 1 `eq` var 1))
    , testCase "exists n. ⌈n⌉" $
        translating (pexists n $ pceil n)
        `yields` exists 0 (fun 1 [var 0])
    , testCase "exists n. ⌈n⌉ and ⌈n < m⌉" $
        translating (pexists n $ pceil n `pand` pceil (n `pleq` m))
        `yields` exists 0 (fun 1 [var 0] `and` fun 2 [var 0])
    , testCase "exists n. (⌈n⌉ and ⌈n < m⌉) and ⌈n⌉" $
        translating
            (pexists n $ (pceil n `pand` pceil (n `pleq` m)) `pand` pceil n)
        `yields`
            exists 0 ((fun 1 [var 0] `and` fun 2 [var 0]) `and` fun 1 [var 0])
    , testCase "(exists n. ⌈n⌉) and ⌈n⌉" $
        translating (pexists n (pceil n) `pand` pceil n)
        `yields` (exists 0 (fun 1 [var 0]) `and` var 2)
    , testCase "(exists n. ⌈n⌉ and n = n) and (exists n. ⌈n⌉)" $
        translating
            (      pexists n (pceil n `pand` (n `peq` n))
            `pand` pexists n (pceil n)
            )
        `yields`
            (     exists 0 (fun 1 [var 0] `and` (var 0 `eq` var 0))
            `and` exists 2 (fun 1 [var 2])
            )
    , testCase "(exists n. exists m. ⌈n⌉ and ⌈m⌉) and (exists n. ⌈n⌉)" $
        translating
            (      pexists n (pexists m (pceil n `pand` pceil m))
            `pand` pexists n (pceil n)
            )
        `yields`
            (     exists 0 (exists 1 (fun 2 [var 0] `and` fun 3 [var 1]))
            `and` exists 4 (fun 2 [var 4])
            )
    , testCase "(exists n. exists m. ⌈n⌉ and ⌈m⌉)\
               \ and (exists m. exists n. ⌈n⌉ and ⌈m⌉)" $
        translating
            (      pexists m (pexists n (pceil n `pand` pceil m))
            `pand` pexists n (pexists m (pceil n `pand` pceil m))
            )
        `yields`
            (     exists 0 (exists 1 (fun 2 [var 1] `and` fun 3 [var 0]))
            `and` exists 4 (exists 5 (fun 2 [var 4] `and` fun 3 [var 5]))
            )
    , testCase "(exists n. exists m. ⌈n⌉ and ⌈m⌉) and (exists m. ⌈n⌉)" $
        translating
            (      pexists n (pexists m (pceil n `pand` pceil m))
            `pand` pexists m (pceil n)
            )
        `yields`
            (     exists 0 (exists 1 (fun 2 [var 0] `and` fun 3 [var 1]))
            `and` exists 4 (var 5)
            )
    , testCase "exists n. exists m. ⌈n < m⌉" $
        translating (pexists n $ pexists m $ pceil (n `pleq` m))
        `yields` exists 0 (exists 1 $ fun 2 [var 0, var 1])
    , testCase "(exists n. exists m. ⌈n < m⌉) and (exists m. exists n. ⌈n < m⌉)"
        $ translating
            (      pexists n (pexists m $ pceil (n `pleq` m))
            `pand` pexists m (pexists n $ pceil (n `pleq` m))
            )
        `yields`
            (     exists 0 (exists 1 $ fun 2 [var 0, var 1])
            `and` exists 3 (exists 4 $ fun 2 [var 4, var 3])
            )
    , testCase "(exists n. exists m. ⌈n < m⌉) and\
              \ (exists m. exists p. exists n. ⌈n < m⌉)"
        $ translating
            (      pexists n (pexists m $ pceil (n `pleq` m))
            `pand` pexists m (pexists k (pexists n $ pceil (n `pleq` m)))
            )
        `yields`
            (     exists 0 (exists 1 $ fun 2 [var 0, var 1])
            `and` exists 3 (existsb 4 $ exists 5 $ fun 2 [var 5, var 3])
            )
    , testCase "(exists n. exists m. ⌈n < m⌉) and\
              \ (exists m. exists x. exists n. ⌈n < m⌉)"
        $ translating
            (      pexists n (pexists m $ pceil (n `pleq` m))
            `pand` pexists m (pexists x (pexists n $ pceil (n `pleq` m)))
            )
        `yields`
            (     exists 0 (exists 1 $ fun 2 [var 0, var 1])
            `and` exists 3 (existst 4 $ exists 5 $ fun 2 [var 5, var 3])
            )
    , testCase "X:Int = X:Int /Int Y:Int" $
        yields
            (translating (peq n (Mock.tdivInt n m)))
            (var 0 `eq` (var 0 `sdiv` var 1))
    , testCase "X:Int = \\defined X:Int /Int Y:Int" $
        yields
            (translating (peq n (TermLike.mkDefined $ Mock.tdivInt n m)))
            (var 0 `eq` (var 0 `sdiv` var 1))
    , testCase "erases predicate sorts" $ do
        -- Two inputs: the same \ceil in different outer sorts.
        let input1 = pceil (Mock.tdivInt n m)
            input2 = pceil' (Mock.tdivInt n m)
        (actual1, actual2) <-
            do
                actual1 <- translatePredicate input1
                actual2 <- translatePredicate input2
                return (actual1, actual2)
            & evalTranslator
            & expectJustT
            & Test.SMT.runNoSMT
        assertEqual "" actual1 actual2
    , testCase "b = a, both constructors" $
            translating (peq Mock.b Mock.a)
        `yields`
            (var 0 `eq` var 1)
    , testCase "f() = a, f functional, a constructor" $
            translating (peq Mock.functional00 Mock.a)
        `yields`
            (var 0 `eq` var 1)
    , testCase "s() = a, s arbitrary symbol, a constructor" $
            translating (peq Mock.plain00 Mock.a)
        `yields`
            var 0
    ]
  where
    x = TermLike.mkElemVar Mock.x
    n = TermLike.mkElemVar Mock.xInt
    m = TermLike.mkElemVar Mock.yInt
    k = TermLike.mkElemVar Mock.xBool
    smtTrue = Atom "true"
    var :: Integer -> SExpr
    var i = Atom $ "<" <> Text.pack (show i) <> ">"
    pleq = Mock.lessInt
    peq = Predicate.makeEqualsPredicate_
    pand = Predicate.makeAndPredicate
    pceil = Predicate.makeCeilPredicate_
    pceil' = Predicate.makeCeilPredicate Mock.intSort
    true = Predicate.makeTruePredicate_
    pexists (TermLike.ElemVar_ v) p = Predicate.makeExistsPredicate v p
    pexists _ _ = undefined
    exists i p = existsQ [List [var i, Atom "Int"]] p
    existsb i p = existsQ [List [var i, Atom "Bool"]] p
    existst i p = existsQ [List [var i, Atom "|HB_testSort|"]] p
    fun i p = SMT.SimpleSMT.List (var i : p)
    sdiv i j = List [Atom "div", i, j]

translatePredicate
    :: HasCallStack
    => Predicate VariableName
    -> Translator NoSMT VariableName SExpr
translatePredicate = Evaluator.translatePredicate Mock.metadataTools

translating :: HasCallStack => Predicate VariableName -> IO (Maybe SExpr)
translating =
    Test.SMT.runNoSMT . runMaybeT . evalTranslator . translatePredicate

yields :: HasCallStack => IO (Maybe SExpr) -> SExpr -> IO ()
actual `yields` expected = actual >>= assertEqual "" (Just expected)
