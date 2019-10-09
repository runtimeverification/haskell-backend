module Test.Kore.Step.SMT.Helpers
    ( atom
    , list
    , eq
    , gt
    , lt
    , ofType
    , isError
    , isNotSatisfiable
    , isSatisfiable
    , constructorAxiom
    , testsForModule
    ) where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Exception
    ( ErrorCall
    , catch
    )
import Data.Reflection
    ( Given
    , give
    )
import Data.Sup
    ( Sup (Element)
    )
import Data.Text
    ( Text
    )
import GHC.Stack
    ( HasCallStack
    )
import Numeric.Natural
    ( Natural
    )

import Kore.Attribute.Attributes
import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin as Builtin
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
    ( build
    )
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import Kore.Syntax.Sentence
    ( ParsedSentence
    , Sentence (..)
    , SentenceAxiom (SentenceAxiom)
    )
import qualified Kore.Syntax.Sentence as SentenceAxiom
    ( SentenceAxiom (..)
    )
import Kore.Syntax.Variable
    ( Variable (Variable)
    )
import SMT
    ( SMT
    )
import qualified SMT

import Test.Kore
    ( testId
    )
import Test.Kore.Builtin.Builtin
    ( runSMT
    )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import Test.Kore.Step.SMT.Builders
    ( noJunk
    )
import Test.Kore.With
    ( with
    )

newtype SmtPrelude = SmtPrelude { getSmtPrelude :: SMT () }

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

isSatisfiable
    :: HasCallStack
    => [SMT ()]
    -> SmtPrelude
    -> TestTree
isSatisfiable = assertSmtTestCase "isSatisfiable" SMT.Sat

isNotSatisfiable
    :: HasCallStack
    => [SMT ()]
    -> SmtPrelude
    -> TestTree
isNotSatisfiable = assertSmtTestCase "isNotSatisfiable" SMT.Unsat

isError
    :: HasCallStack
    => [SMT ()]
    -> SmtPrelude
    -> TestTree
isError actions prelude =
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

getSmtResult
    :: [SMT ()]
    -> SmtPrelude
    -> IO SMT.Result
getSmtResult
    actions
    SmtPrelude {getSmtPrelude = preludeAction}
  = do
    let
        smtResult :: SMT SMT.Result
        smtResult = do
            preludeAction
            sequence_ actions
            SMT.check
    runSMT smtResult

assertSmtResult
    :: HasCallStack
    => SMT.Result
    -> [SMT ()]
    -> SmtPrelude
    -> Assertion
assertSmtResult expected actions prelude = do
    result <- getSmtResult actions prelude
    assertEqual "" expected result

assertSmtTestCase
    :: HasCallStack
    => String
    -> SMT.Result
    -> [SMT ()]
    -> SmtPrelude
    -> TestTree
assertSmtTestCase name expected actions prelude =
    testCase name $ assertSmtResult expected actions prelude

testsForModule
    :: String
    ->  ( forall m
        .   ( Given (SmtMetadataTools Attribute.Symbol)
            , SMT.MonadSMT m
            )
        => VerifiedModule Attribute.Symbol Attribute.Axiom
        -> m ()
        )
    -> VerifiedModule Attribute.Symbol Attribute.Axiom
    -> [SmtPrelude -> TestTree]
    -> TestTree
testsForModule name functionToTest indexedModule tests =
    testGroup name (map (\f -> f prelude) tests)
  where
    prelude = SmtPrelude
        (give tools $ functionToTest indexedModule)
    tools = MetadataTools.build indexedModule

constructorAxiom :: Text -> [(Text, [Text])] -> ParsedSentence
constructorAxiom sortName constructors =
    SentenceAxiomSentence SentenceAxiom
        { sentenceAxiomParameters = []
        , sentenceAxiomPattern =
            Builtin.externalize
            $ foldr mkOr (mkBottom sort) constructorAssertions
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
        argumentVariables :: [ElementVariable Variable]
        argumentVariables = zipWith makeVariable [1..] argumentSorts

        symbol =
            Symbol
                { symbolConstructor = testId constructorName
                , symbolParams      = []
                , symbolAttributes  = Mock.constructorFunctionalAttributes
                , symbolSorts       =
                    applicationSorts (map makeSort argumentSorts) sort
                }

makeVariable :: Natural -> Text -> ElementVariable Variable
makeVariable varIndex sortName = ElementVariable
    Variable
        { variableName = testId "var"
        , variableCounter = Just (Element varIndex)
        , variableSort = makeSort sortName
        }

makeSort :: Text -> Sort
makeSort name =
    SortActualSort SortActual
        { sortActualName  = testId name
        , sortActualSorts = []
        }
