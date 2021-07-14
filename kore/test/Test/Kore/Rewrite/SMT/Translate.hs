module Test.Kore.Rewrite.SMT.Translate (
    test_translatePredicateWith,
) where

import Control.Error (
    runMaybeT,
 )
import qualified Data.HashSet as HashSet
import Data.Reflection (
    give,
 )
import qualified Data.Text as Text
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike (
    TermLike,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
import qualified Kore.Rewrite.SMT.Evaluator as Evaluator
import Kore.Rewrite.SMT.Translate (
    Translator,
    evalTranslator,
 )
import qualified Kore.Rewrite.SMT.Translate as SMT
import Prelude.Kore hiding (
    and,
 )
import SMT
import qualified SMT.SimpleSMT
import Test.Expect
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import qualified Test.SMT
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_translatePredicateWith :: [TestTree]
test_translatePredicateWith =
    [ testCase "true" $
        translatingPred true `yields` smtTrue
    , testCase "n = n" $
        translatingPred (n `peq` n)
            `yields` (var 0 `eq` var 0)
    , testCase "exists n. true" $
        translatingPred (pexists n true)
            `yields` smtTrue
    , testCase "exists n. n = n" $
        translatingPred (pexists n $ n `peq` n)
            `yields` exists 0 (var 0 `eq` var 0)
    , testCase "exists n. n = m" $
        translatingPred (pexists n $ n `peq` m)
            `yields` exists 0 (var 0 `eq` var 1)
    , testCase "exists x. x = x where x not of a builtin sort" $
        translatingPred (pexists x $ x `peq` x)
            `yields` existst 0 (var 0 `eq` var 0)
    , testCase "n = n and (exists n. n = n)" $
        translatingPred ((n `peq` n) `pand` pexists n (n `peq` n))
            `yields` ((var 0 `eq` var 0) `and` exists 1 (var 1 `eq` var 1))
    , testCase "exists n. ⌈n⌉" $
        translatingPred (pexists n $ pceil n)
            `yields` exists 0 (fun 1 [var 0])
    , testCase "exists n. ⌈n⌉ and ⌈n < m⌉" $
        translatingPred (pexists n $ pceil n `pand` pceil (n `pleq` m))
            `yields` exists 0 (fun 1 [var 0] `and` fun 2 [var 0])
    , testCase "exists n. (⌈n⌉ and ⌈n < m⌉) and ⌈n⌉" $
        translatingPred
            (pexists n $ (pceil n `pand` pceil (n `pleq` m)) `pand` pceil n)
            `yields` exists 0 ((fun 1 [var 0] `and` fun 2 [var 0]) `and` fun 1 [var 0])
    , testCase "(exists n. ⌈n⌉) and ⌈n⌉" $
        translatingPred (pexists n (pceil n) `pand` pceil n)
            `yields` (exists 0 (fun 1 [var 0]) `and` var 2)
    , testCase "(exists n. ⌈n⌉ and n = n) and (exists n. ⌈n⌉)" $
        translatingPred
            ( pexists n (pceil n `pand` (n `peq` n))
                `pand` pexists n (pceil n)
            )
            `yields` ( exists 0 (fun 1 [var 0] `and` (var 0 `eq` var 0))
                        `and` exists 2 (fun 1 [var 2])
                     )
    , testCase "(exists n. exists m. ⌈n⌉ and ⌈m⌉) and (exists n. ⌈n⌉)" $
        translatingPred
            ( pexists n (pexists m (pceil n `pand` pceil m))
                `pand` pexists n (pceil n)
            )
            `yields` ( exists 0 (exists 1 (fun 2 [var 0] `and` fun 3 [var 1]))
                        `and` exists 4 (fun 2 [var 4])
                     )
    , testCase
        "(exists n. exists m. ⌈n⌉ and ⌈m⌉)\
        \ and (exists m. exists n. ⌈n⌉ and ⌈m⌉)"
        $ translatingPred
            ( pexists m (pexists n (pceil n `pand` pceil m))
                `pand` pexists n (pexists m (pceil n `pand` pceil m))
            )
            `yields` ( exists 0 (exists 1 (fun 2 [var 1] `and` fun 3 [var 0]))
                        `and` exists 4 (exists 5 (fun 2 [var 4] `and` fun 3 [var 5]))
                     )
    , testCase "(exists n. exists m. ⌈n⌉ and ⌈m⌉) and (exists m. ⌈n⌉)" $
        translatingPred
            ( pexists n (pexists m (pceil n `pand` pceil m))
                `pand` pexists m (pceil n)
            )
            `yields` ( exists 0 (exists 1 (fun 2 [var 0] `and` fun 3 [var 1]))
                        `and` exists 4 (var 5)
                     )
    , testCase "exists n. exists m. ⌈n < m⌉" $
        translatingPred (pexists n $ pexists m $ pceil (n `pleq` m))
            `yields` exists 0 (exists 1 $ fun 2 [var 0, var 1])
    , testCase "(exists n. exists m. ⌈n < m⌉) and (exists m. exists n. ⌈n < m⌉)" $
        translatingPred
            ( pexists n (pexists m $ pceil (n `pleq` m))
                `pand` pexists m (pexists n $ pceil (n `pleq` m))
            )
            `yields` ( exists 0 (exists 1 $ fun 2 [var 0, var 1])
                        `and` exists 3 (exists 4 $ fun 2 [var 4, var 3])
                     )
    , testCase
        "(exists n. exists m. ⌈n < m⌉) and\
        \ (exists m. exists p. exists n. ⌈n < m⌉)"
        $ translatingPred
            ( pexists n (pexists m $ pceil (n `pleq` m))
                `pand` pexists m (pexists k (pexists n $ pceil (n `pleq` m)))
            )
            `yields` ( exists 0 (exists 1 $ fun 2 [var 0, var 1])
                        `and` exists 3 (existsb 4 $ exists 5 $ fun 2 [var 5, var 3])
                     )
    , testCase
        "(exists n. exists m. ⌈n < m⌉) and\
        \ (exists m. exists x. exists n. ⌈n < m⌉)"
        $ translatingPred
            ( pexists n (pexists m $ pceil (n `pleq` m))
                `pand` pexists m (pexists x (pexists n $ pceil (n `pleq` m)))
            )
            `yields` ( exists 0 (exists 1 $ fun 2 [var 0, var 1])
                        `and` exists 3 (existst 4 $ exists 5 $ fun 2 [var 5, var 3])
                     )
    , testCase "X:Int = X:Int /Int Y:Int" $
        yields
            (translatingPred (peq n (Mock.tdivInt n m)))
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
    , -- In the tests below, a and b are not tranlated correctly
      -- to their constructor names because they need to be
      -- declared twice in the test data: once as part of their
      -- sort and once as symbols.
      testCase "b = a, both constructors" $
        translatingPred (peq Mock.b Mock.a)
            `yields` (var 0 `eq` var 1)
    , testCase "f() = a, f functional, a constructor" $
        translatingPred (peq Mock.functional00 Mock.a)
            `yields` (Atom "functional00" `eq` var 0)
    , testCase "s() = a, s arbitrary symbol, a constructor" $
        translatingPred (peq Mock.plain00 Mock.a)
            `yields` var 0
    , -- This should fail because we don't know if it is defined.
      -- , testCase "function(x)" $
      --     translatingPatt SideCondition.top (Mock.functionSMT x) & fails
      -- -- This should fail because we don't know if it is defined.
      -- , testCase "functional(function(x))" $
      --     translatingPatt
      --         SideCondition.top
      --         (Mock.functionalSMT (Mock.functionSMT x))
      --     & fails
      testCase "function(x), where function(x) is defined" $
        translatingPatt (defined (function x)) (function x)
            `yields` functionSMT (var 0)
    , testCase "functional(function(x)) where function(x) is defined" $
        translatingPatt
            (defined (functional (function x)))
            (functional (function x))
            `yields` functionalSMT (functionSMT (var 0))
    ]
  where
    x = TermLike.mkElemVar Mock.x
    n = TermLike.mkElemVar Mock.xInt
    m = TermLike.mkElemVar Mock.yInt
    k = TermLike.mkElemVar Mock.xBool
    smtTrue = Atom "true"
    var :: Integer -> SExpr
    var i = Atom $ "<" <> Text.pack (show i) <> ">"
    function = Mock.functionSMT
    functional = Mock.functionalSMT
    functionSMT sexpr = List [Atom "functionSMT", sexpr]
    functionalSMT sexpr = List [Atom "functionalSMT", sexpr]
    pleq = Mock.lessInt
    peq = Predicate.makeEqualsPredicate
    pand = Predicate.makeAndPredicate
    pceil = Predicate.makeCeilPredicate
    pceil' = Predicate.makeCeilPredicate
    true = Predicate.makeTruePredicate
    pexists (TermLike.ElemVar_ v) p = Predicate.makeExistsPredicate v p
    pexists _ _ = undefined
    exists i p = existsQ [List [var i, Atom "Int"]] p
    existsb i p = existsQ [List [var i, Atom "Bool"]] p
    existst i p = existsQ [List [var i, Atom "|HB_testSort|"]] p
    fun i p = SMT.SimpleSMT.List (var i : p)
    sdiv i j = List [Atom "div", i, j]
    defined term =
        term
            & HashSet.singleton
            & SideCondition.fromDefinedTerms

translatePredicate ::
    HasCallStack =>
    Predicate VariableName ->
    Translator VariableName NoSMT SExpr
translatePredicate =
    Evaluator.translatePredicate SideCondition.top Mock.metadataTools

translatePattern ::
    HasCallStack =>
    SideCondition VariableName ->
    TermLike VariableName ->
    Translator VariableName NoSMT SExpr
translatePattern sideCondition =
    give Mock.metadataTools $
        SMT.translatePattern
            sideCondition
            Evaluator.translateTerm
            Mock.testSort

translatingPred :: HasCallStack => Predicate VariableName -> IO (Maybe SExpr)
translatingPred =
    Test.SMT.runNoSMT . runMaybeT . evalTranslator . translatePredicate

translatingPatt ::
    HasCallStack =>
    SideCondition VariableName ->
    TermLike VariableName ->
    IO (Maybe SExpr)
translatingPatt sideCondition =
    Test.SMT.runNoSMT
        . runMaybeT
        . evalTranslator
        . translatePattern sideCondition

yields :: HasCallStack => IO (Maybe SExpr) -> SExpr -> IO ()
actual `yields` expected = actual >>= assertEqual "" (Just expected)

--
-- fails :: HasCallStack => IO (Maybe SExpr) -> IO ()
-- fails actual = actual >>= assertEqual "" Nothing
