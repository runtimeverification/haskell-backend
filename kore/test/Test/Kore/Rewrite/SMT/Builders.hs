module Test.Kore.Rewrite.SMT.Builders (
    emptyModule,
    sortDeclaration,
    hookedSortDeclaration,
    symbolDeclaration,
    indexModule,
    indexModules,
    -- Attributes
    constructor,
    functional,
    hook,
    noJunk,
    smthook,
    smtlib,
    -- Kore AST
    koreSort,
) where

import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import qualified Kore.Attribute.Constructor as Constructor
import qualified Kore.Attribute.Functional as Functional
import qualified Kore.Attribute.Hook as Hook
import qualified Kore.Attribute.Smthook as Smthook
import qualified Kore.Attribute.Smtlib as Smtlib
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Builtin as Builtin
import Kore.Error (
    Error,
 )
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Sort (
    Sort (SortActualSort),
    SortActual (SortActual),
 )
import qualified Kore.Sort as SortActual (
    SortActual (..),
 )
import Kore.Syntax.Definition
import Kore.Validate.DefinitionVerifier (
    verifyAndIndexDefinition,
 )
import Kore.Validate.Error (
    VerifyError,
 )
import Prelude.Kore
import Test.Kore (
    testId,
 )
import Test.Kore.With (
    Attribute (Attribute),
 )

indexModule ::
    ParsedModule ->
    VerifiedModule Attribute.Symbol
indexModule m@Module{moduleName} =
    indexModules moduleName [m]

indexModules ::
    ModuleName ->
    [ParsedModule] ->
    VerifiedModule Attribute.Symbol
indexModules moduleName modules =
    case perhapsIndexedDefinition of
        Left err ->
            (error . unlines)
                [ "Cannot index definition:"
                , "err = " ++ show err
                , "modules = " ++ show modules
                ]
        Right indexedModules ->
            case Map.lookup moduleName indexedModules of
                Just indexed -> indexed
                _ ->
                    error
                        "Expected to find the module in indexed definition."
  where
    perhapsIndexedDefinition ::
        Either
            (Error VerifyError)
            (Map.Map ModuleName (VerifiedModule Attribute.Symbol))
    perhapsIndexedDefinition =
        verifyAndIndexDefinition
            Builtin.koreVerifiers
            Definition
                { definitionAttributes = Attributes []
                , definitionModules = modules
                }

-- TODO(virgil): either use an attribute called noJunk, or rename
-- this constant
noJunk :: Attribute
noJunk = constructor

constructor :: Attribute
constructor = Attribute Constructor.constructorAttribute

functional :: Attribute
functional = Attribute Functional.functionalAttribute

smtlib :: Text -> Attribute
smtlib value = Attribute (Smtlib.smtlibAttribute value)

smthook :: Text -> Attribute
smthook value = Attribute (Smthook.smthookAttribute value)

hook :: Text -> Attribute
hook value = Attribute (Hook.hookAttribute value)

koreSort :: Text -> Sort
koreSort name =
    SortActualSort
        SortActual
            { sortActualName = testId name
            , sortActualSorts = []
            }

emptyModule :: Text -> Module sentence
emptyModule name =
    Module
        { moduleName = ModuleName name
        , moduleSentences = []
        , moduleAttributes = Attributes []
        }

sortDeclaration :: Text -> ParsedSentence
sortDeclaration name =
    asSentence
        SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

hookedSortDeclaration :: Text -> ParsedSentence
hookedSortDeclaration name =
    (asSentence . SentenceHookedSort)
        SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

symbolDeclaration :: Text -> Text -> [Text] -> ParsedSentence
symbolDeclaration name sortName argumentSortNames =
    asSentence
        SentenceSymbol
            { sentenceSymbolSymbol = makeSymbol name
            , sentenceSymbolSorts = map koreSort argumentSortNames
            , sentenceSymbolResultSort = koreSort sortName
            , sentenceSymbolAttributes = Attributes []
            }

makeSymbol :: Text -> Symbol
makeSymbol name =
    Symbol
        { symbolConstructor = testId name
        , symbolParams = []
        }
