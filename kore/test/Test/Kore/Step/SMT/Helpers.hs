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

import           Kore.AST.Common
                 ( SymbolOrAlias (SymbolOrAlias), Variable (Variable) )
import           Kore.AST.Common as Variable
                 ( Variable (..) )
import           Kore.AST.Common as SymbolOrAlias
                 ( SymbolOrAlias (..) )
import           Kore.AST.Kore
                 ( eraseAnnotations )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureToKore
                 ( patternPureToKore )
import           Kore.AST.Sentence
                 ( Attributes (Attributes), KoreSentence,
                 SentenceAxiom (SentenceAxiom), asKoreAxiomSentence )
import qualified Kore.AST.Sentence as SentenceAxiom
                 ( SentenceAxiom (..) )
import           Kore.AST.Valid
                 ( mkApp, mkBottom, mkExists, mkOr, mkVar )
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, extractMetadataTools )
import           Kore.Sort
                 ( Sort (SortActualSort), SortActual (SortActual) )
import qualified Kore.Sort as SortActual
                 ( SortActual (..) )
import           SMT
                 ( SMT )
import qualified SMT

import Test.Kore
       ( testId )
import Test.Kore.Step.SMT.Builders
       ( noJunk, with )
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
        .   ( Given (MetadataTools Object Attribute.Symbol)
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
    tools = extractMetadataTools indexedModule

constructorAxiom :: Text -> [(Text, [Text])] -> KoreSentence
constructorAxiom sortName constructors =
    asKoreAxiomSentence
        SentenceAxiom
            { sentenceAxiomParameters = []
            , sentenceAxiomPattern =
                eraseAnnotations
                $ patternPureToKore
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
        argumentVariables :: [Variable Object]
        argumentVariables = zipWith makeVariable [1..] argumentSorts

makeVariable :: Natural -> Text -> Variable Object
makeVariable varIndex sortName =
    Variable
        { variableName = testId "var"
        , variableCounter = Just (Element varIndex)
        , variableSort = makeSort sortName
        }

makeSort :: Text -> Sort Object
makeSort name =
    SortActualSort SortActual
        { sortActualName  = testId name
        , sortActualSorts = []
        }

makeHead :: Text -> SymbolOrAlias Object
makeHead name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams      = []
        }
