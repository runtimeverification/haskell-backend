module Test.Kore.Step.SMT.Translate
    ( test_goTranslatePredicate
    ) where

import Prelude.Kore hiding
    ( and
    )

import Test.Tasty

import Control.Error
    ( runMaybeT
    )
import qualified Data.Text as Text

import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.SMT
import Test.Tasty.HUnit.Ext

import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
import qualified Kore.Step.SMT.Evaluator as Evaluator
import Kore.Step.SMT.Translate
    ( evalTranslator
    )
import SMT
import qualified SMT.SimpleSMT

test_goTranslatePredicate :: [TestTree]
test_goTranslatePredicate =
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
    true = Predicate.makeTruePredicate_
    pexists (TermLike.ElemVar_ v) p = Predicate.makeExistsPredicate v p
    pexists _ _ = undefined
    exists i p = existsQ [List [var i, Atom "Int"]] p
    existsb i p = existsQ [List [var i, Atom "Bool"]] p
    existst i p = existsQ [List [var i, Atom "|HB_testSort|"]] p
    fun i p = SMT.SimpleSMT.List (var i : p)

translating :: HasCallStack => Predicate VariableName -> IO (Maybe SExpr)
translating =
    Test.SMT.runNoSMT . runMaybeT . evalTranslator
    . Evaluator.translatePredicate Mock.metadataTools


yields :: HasCallStack => IO (Maybe SExpr) -> SExpr -> IO ()
actual `yields` expected = actual >>= assertEqual "" (Just expected)
