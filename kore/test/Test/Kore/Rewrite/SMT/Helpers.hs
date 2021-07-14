module Test.Kore.Rewrite.SMT.Helpers (
    atom,
    list,
    eq,
    gt,
    lt,
    ofType,
    isError,
    isNotSatisfiable,
    isSatisfiable,
    isSatisfiableWithTools,
    isNotSatisfiableWithTools,
    constructorAxiom,
    testsForModule,
) where

import Control.Exception (
    ErrorCall,
    catch,
 )
import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import Data.Limit
import Data.Reflection (
    Given,
    give,
 )
import Data.Sup (
    Sup (Element),
 )
import Data.Text (
    Text,
 )
import Kore.Attribute.Attributes
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools (
    build,
 )
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Syntax.Sentence (
    ParsedSentence,
    Sentence (..),
    SentenceAxiom (SentenceAxiom),
 )
import qualified Kore.Syntax.Sentence as SentenceAxiom (
    SentenceAxiom (..),
 )
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore
import SMT (
    Config (..),
    SMT,
    TimeOut (..),
    defaultConfig,
 )
import qualified SMT
import Test.Kore (
    testId,
 )
import Test.Kore.Builtin.Builtin (
    runSMTWithConfig,
 )
import Test.Kore.Builtin.External
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import Test.Kore.Rewrite.SMT.Builders (
    noJunk,
 )
import Test.Kore.With (
    with,
 )
import Test.Tasty
import Test.Tasty.HUnit

newtype SmtPrelude = SmtPrelude {getSmtPrelude :: SMT ()}

ofType :: SMT.MonadSMT m => Text -> Text -> m ()
name `ofType` constType = do
    _ <- SMT.declare name (atom constType)
    return ()

atom :: Text -> SMT.SExpr
atom = SMT.Atom

list :: [SMT.SExpr] -> SMT.SExpr
list = SMT.List

gt :: SMT.SExpr -> SMT.SExpr -> SMT.SExpr
gt = SMT.gt

lt :: SMT.SExpr -> SMT.SExpr -> SMT.SExpr
lt = SMT.lt

eq :: SMT.SExpr -> SMT.SExpr -> SMT.SExpr
eq = SMT.eq

isSatisfiable ::
    HasCallStack =>
    [SMT ()] ->
    SmtMetadataTools Attribute.Symbol ->
    SmtPrelude ->
    TestTree
isSatisfiable tests _ = assertSmtTestCase "isSatisfiable" SMT.Sat tests

isSatisfiableWithTools ::
    HasCallStack =>
    [SmtMetadataTools Attribute.Symbol -> SMT ()] ->
    SmtMetadataTools Attribute.Symbol ->
    SmtPrelude ->
    TestTree
isSatisfiableWithTools tests tools prelude =
    assertSmtTestCase
        "isSatisfiable"
        SMT.Sat
        (fmap (\t -> t tools) tests)
        prelude

isNotSatisfiable ::
    HasCallStack =>
    [SMT ()] ->
    SmtMetadataTools Attribute.Symbol ->
    SmtPrelude ->
    TestTree
isNotSatisfiable tests _ = assertSmtTestCase "isNotSatisfiable" SMT.Unsat tests

isNotSatisfiableWithTools ::
    HasCallStack =>
    [SmtMetadataTools Attribute.Symbol -> SMT ()] ->
    SmtMetadataTools Attribute.Symbol ->
    SmtPrelude ->
    TestTree
isNotSatisfiableWithTools tests tools prelude =
    assertSmtTestCase
        "isNotSatisfiable"
        SMT.Unsat
        (fmap (\t -> t tools) tests)
        prelude

isError ::
    HasCallStack =>
    [SMT ()] ->
    SmtMetadataTools Attribute.Symbol ->
    SmtPrelude ->
    TestTree
isError actions _ prelude =
    testCase "isError" $
        catch (catch runSolver ignoreIOError) ignoreErrorCall
  where
    runSolver = do
        _ <- getSmtResult actions prelude
        assertFailure "No `error` was raised."

    ignoreIOError :: IOError -> IO ()
    ignoreIOError _err =
        return ()

    ignoreErrorCall :: ErrorCall -> IO ()
    ignoreErrorCall _err =
        return ()

getSmtResult ::
    [SMT ()] ->
    SmtPrelude ->
    IO SMT.Result
getSmtResult
    actions
    SmtPrelude{getSmtPrelude = preludeAction} =
        do
            let smtResult :: SMT SMT.Result
                smtResult = do
                    sequence_ actions
                    SMT.check
            runSMTWithConfig
                defaultConfig{timeOut = TimeOut (Limit 100)}
                preludeAction
                smtResult

assertSmtResult ::
    HasCallStack =>
    SMT.Result ->
    [SMT ()] ->
    SmtPrelude ->
    Assertion
assertSmtResult expected actions prelude = do
    result <- getSmtResult actions prelude
    assertEqual "" expected result

assertSmtTestCase ::
    HasCallStack =>
    String ->
    SMT.Result ->
    [SMT ()] ->
    SmtPrelude ->
    TestTree
assertSmtTestCase name expected actions prelude =
    testCase name $ assertSmtResult expected actions prelude

testsForModule ::
    String ->
    ( forall m.
      ( Given (SmtMetadataTools Attribute.Symbol)
      , SMT.MonadSMT m
      ) =>
      VerifiedModule Attribute.Symbol ->
      m ()
    ) ->
    VerifiedModule Attribute.Symbol ->
    [SmtMetadataTools Attribute.Symbol -> SmtPrelude -> TestTree] ->
    TestTree
testsForModule name functionToTest indexedModule tests =
    testGroup name (map (\f -> f tools prelude) tests)
  where
    prelude =
        SmtPrelude
            (give tools $ functionToTest indexedModule)
    tools = MetadataTools.build indexedModule

constructorAxiom :: Text -> [(Text, [Text])] -> ParsedSentence
constructorAxiom sortName constructors =
    SentenceAxiomSentence
        SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern =
                externalize $
                    foldr mkOr (mkBottom sort) constructorAssertions
            , sentenceAxiomAttributes = Attributes []
            }
        `with` noJunk
  where
    sort = makeSort sortName
    constructorAssertions =
        map constructorAssertion constructors
    constructorAssertion (constructorName, argumentSorts) =
        foldr
            mkExists
            (mkApplySymbol symbol (map mkElemVar argumentVariables))
            argumentVariables
      where
        argumentVariables :: [ElementVariable VariableName]
        argumentVariables = zipWith makeVariable [1 ..] argumentSorts

        symbol =
            Symbol
                { symbolConstructor = testId constructorName
                , symbolParams = []
                , symbolAttributes = Mock.constructorFunctionalAttributes
                , symbolSorts =
                    applicationSorts (map makeSort argumentSorts) sort
                }

makeVariable :: Natural -> Text -> ElementVariable VariableName
makeVariable varIndex sortName =
    mkElementVariable (testId "var") (makeSort sortName)
        & Lens.set
            (field @"variableName" . Lens.mapped . field @"counter")
            (Just (Element varIndex))

makeSort :: Text -> Sort
makeSort name =
    SortActualSort
        SortActual
            { sortActualName = testId name
            , sortActualSorts = []
            }
