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

import Control.Concurrent.MVar
       ( MVar )
import Control.Exception
       ( ErrorCall, catch )
import Control.Monad.Reader
       ( runReaderT )
import Data.Reflection
       ( Given, give )
import Data.Sup
       ( Sup (Element) )
import Data.Text
       ( Text )
import GHC.Stack
       ( HasCallStack )
import Numeric.Natural
       ( Natural )

import qualified Kore.Attribute.Axiom as Attribute
                 ( Axiom )
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import qualified Kore.Builtin as Builtin
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
                 ( build )
import           Kore.Internal.TermLike
import           Kore.Syntax.Application
                 ( SymbolOrAlias (SymbolOrAlias) )
import           Kore.Syntax.Application as SymbolOrAlias
                 ( SymbolOrAlias (..) )
import qualified Kore.Syntax.Sentence as SentenceAxiom
                 ( SentenceAxiom (..) )
import           Kore.Syntax.Variable
                 ( Variable (Variable) )
import           SMT
                 ( SMT )
import qualified SMT

import Test.Kore
       ( testId )
import Test.Kore.Step.SMT.Builders
       ( noJunk )
import Test.Kore.With
       ( with )
import Test.SMT
       ( withSolver )

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
    -> IO (MVar SMT.Solver)
    -> TestTree
isSatisfiable = assertSmtTestCase "isSatisfiable" SMT.Sat

isNotSatisfiable
    :: HasCallStack
    => [SMT ()]
    -> SmtPrelude
    -> IO (MVar SMT.Solver)
    -> TestTree
isNotSatisfiable = assertSmtTestCase "isNotSatisfiable" SMT.Unsat

isError
    :: HasCallStack
    => [SMT ()]
    -> SmtPrelude
    -> IO (MVar SMT.Solver)
    -> TestTree
isError actions prelude solver =
    testCase "isError" $
        catch (catch runSolver ignoreIOError) ignoreErrorCall
    where
    runSolver = do
        _ <- getSmtResult actions prelude solver
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
    -> IO (MVar SMT.Solver)
    -> IO SMT.Result
getSmtResult
    actions
    SmtPrelude {getSmtPrelude = preludeAction}
    solverAction
  = do
    let
        smtResult :: SMT SMT.Result
        smtResult = do
            preludeAction
            sequence_ actions
            SMT.check
    solver <- solverAction
    runReaderT (SMT.getSMT (SMT.inNewScope smtResult)) solver

assertSmtResult
    :: HasCallStack
    => SMT.Result
    -> [SMT ()]
    -> SmtPrelude
    -> IO (MVar SMT.Solver)
    -> Assertion
assertSmtResult expected actions prelude solver = do
    result <- getSmtResult actions prelude solver
    assertEqual "" expected result

assertSmtTestCase
    :: HasCallStack
    => String
    -> SMT.Result
    -> [SMT ()]
    -> SmtPrelude
    -> IO (MVar SMT.Solver)
    -> TestTree
assertSmtTestCase name expected actions prelude solver =
    testCase name $ assertSmtResult expected actions prelude solver

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
    -> [SmtPrelude -> IO (MVar SMT.Solver) -> TestTree]
    -> TestTree
testsForModule name functionToTest indexedModule tests =
    testGroup name (map (\f -> withSolver $ f prelude) tests)
  where
    prelude = SmtPrelude
        (give tools $ functionToTest indexedModule)
    tools = MetadataTools.build indexedModule

constructorAxiom :: Text -> [(Text, [Text])] -> ParsedSentence
constructorAxiom sortName constructors =
    SentenceAxiomSentence SentenceAxiom
        { sentenceAxiomParameters = []
        , sentenceAxiomPattern =
            Builtin.externalizePattern
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
            (mkApp
                sort
                (makeHead constructorName)
                (map mkVar argumentVariables)
            )
            argumentVariables
        where
        argumentVariables :: [Variable]
        argumentVariables = zipWith makeVariable [1..] argumentSorts

makeVariable :: Natural -> Text -> Variable
makeVariable varIndex sortName =
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

makeHead :: Text -> SymbolOrAlias
makeHead name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams      = []
        }
