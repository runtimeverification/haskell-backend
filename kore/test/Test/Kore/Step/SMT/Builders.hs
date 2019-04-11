module Test.Kore.Step.SMT.Builders
    ( With (..)
    , emptyModule
    , sortDeclaration
    , symbolDeclaration

    , indexModule
    , indexModules

    -- Attributes
    , noJunk
    , constructor
    , smtlib
    , hook
    ) where

import qualified Data.Map.Strict as Map
import           Data.Text
                 ( Text )

import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Sentence
                 ( Attributes (Attributes), Definition (Definition),
                 KoreSentence, Module (Module), ModuleName (ModuleName),
                 Sentence (SentenceAliasSentence, SentenceAxiomSentence, SentenceClaimSentence, SentenceHookSentence, SentenceImportSentence, SentenceSortSentence, SentenceSymbolSentence),
                 SentenceAlias (SentenceAlias), SentenceAxiom (SentenceAxiom),
                 SentenceHook (SentenceHookedSort, SentenceHookedSymbol),
                 SentenceImport (SentenceImport), SentenceSort (SentenceSort),
                 SentenceSymbol (SentenceSymbol), Symbol (Symbol),
                 UnifiedSentence (UnifiedObjectSentence), asSentence )
import qualified Kore.AST.Sentence as Definition
                 ( Definition (..) )
import qualified Kore.AST.Sentence as Module
                 ( Module (..) )
import qualified Kore.AST.Sentence as SentenceAxiom
                 ( SentenceAxiom (..) )
import qualified Kore.AST.Sentence as SentenceAlias
                 ( SentenceAlias (..) )
import qualified Kore.AST.Sentence as SentenceImport
                 ( SentenceImport (..) )
import qualified Kore.AST.Sentence as SentenceSort
                 ( SentenceSort (..) )
import qualified Kore.AST.Sentence as SentenceSymbol
                 ( SentenceSymbol (..) )
import qualified Kore.AST.Sentence as Symbol
                 ( Symbol (..) )
import           Kore.ASTVerifier.AttributesVerifier
                 ( AttributesVerification (DoNotVerifyAttributes) )
import           Kore.ASTVerifier.DefinitionVerifier
                 ( verifyAndIndexDefinition )
import           Kore.ASTVerifier.Error
                 ( VerifyError )
import qualified Kore.Attribute.Axiom as Attribute
                 ( Axiom )
import qualified Kore.Attribute.Constructor as Constructor
import qualified Kore.Attribute.Hook as Hook
import qualified Kore.Attribute.Smtlib as Smtlib
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( Error )
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.Sort
                 ( Sort (SortActualSort), SortActual (SortActual) )
import qualified Kore.Sort as SortActual
                 ( SortActual (..) )

import Test.Kore
       ( testId )

class With a b where
    with :: a -> b -> a

newtype Attribute = Attribute {getAttribute :: CommonKorePattern}

instance With (Module sentence) Attribute where
    with
        m@Module {moduleAttributes = Attributes as}
        Attribute {getAttribute}
      = m { Module.moduleAttributes = Attributes (getAttribute:as) }

instance With (Definition sentence) Attribute where
    with
        d@Definition {definitionAttributes = Attributes as}
        Attribute {getAttribute}
      = d { Definition.definitionAttributes = Attributes (getAttribute:as) }

instance With (UnifiedSentence variable patt) Attribute where
    (UnifiedObjectSentence s) `with` attribute =
        UnifiedObjectSentence (s `with` attribute)

instance With (Sentence level sort patt) Attribute where
    (SentenceAliasSentence s) `with` attribute =
        SentenceAliasSentence (s `with` attribute)
    (SentenceSymbolSentence s) `with` attribute =
        SentenceSymbolSentence (s `with` attribute)
    (SentenceImportSentence s) `with` attribute =
        SentenceImportSentence (s `with` attribute)
    (SentenceAxiomSentence s) `with` attribute =
        SentenceAxiomSentence (s `with` attribute)
    (SentenceClaimSentence s) `with` attribute =
        SentenceClaimSentence (s `with` attribute)
    (SentenceSortSentence s) `with` attribute =
        SentenceSortSentence (s `with` attribute)
    (SentenceHookSentence (SentenceHookedSort s)) `with` attribute =
        SentenceHookSentence (SentenceHookedSort (s `with` attribute))
    (SentenceHookSentence (SentenceHookedSymbol s)) `with` attribute =
        SentenceHookSentence (SentenceHookedSymbol (s `with` attribute))

instance With (SentenceAlias level patt) Attribute where
    s@SentenceAlias {sentenceAliasAttributes} `with` attribute =
        s
            { SentenceAlias.sentenceAliasAttributes =
                sentenceAliasAttributes `with` attribute
            }

instance With (SentenceAxiom sort patt) Attribute where
    s@SentenceAxiom {sentenceAxiomAttributes} `with` attribute =
        s
            { SentenceAxiom.sentenceAxiomAttributes =
                sentenceAxiomAttributes `with` attribute
            }

instance With (SentenceImport patt) Attribute where
    s@SentenceImport {sentenceImportAttributes} `with` attribute =
        s
            { SentenceImport.sentenceImportAttributes =
                sentenceImportAttributes `with` attribute
            }

instance With (SentenceSymbol level patt) Attribute where
    s@SentenceSymbol {sentenceSymbolAttributes} `with` attribute =
        s
            { SentenceSymbol.sentenceSymbolAttributes =
                sentenceSymbolAttributes `with` attribute
            }

instance With (SentenceSort level patt) Attribute where
    s@SentenceSort {sentenceSortAttributes} `with` attribute =
        s
            { SentenceSort.sentenceSortAttributes =
                sentenceSortAttributes `with` attribute
            }

instance With Attributes Attribute where
    (Attributes attributes) `with` Attribute {getAttribute} =
        Attributes (getAttribute:attributes)

instance With (Module sentence) sentence where
    with
        m@Module {moduleSentences = sentences}
        sentence
      = m { Module.moduleSentences = sentence : sentences }

indexModule
    :: Module KoreSentence
    -> VerifiedModule Attribute.Symbol Attribute.Axiom
indexModule m@Module{ moduleName } =
    indexModules moduleName [m]

indexModules
    :: ModuleName
    -> [Module KoreSentence]
    -> VerifiedModule Attribute.Symbol Attribute.Axiom
indexModules moduleName modules =
    case perhapsIndexedDefinition of
        Left err -> (error .unlines)
            [ "Cannot index definition:"
            , "err = " ++ show err
            , "modules = " ++ show modules
            ]
        Right indexedModules ->
            case Map.lookup moduleName indexedModules of
                Just indexed -> indexed
                _ -> error
                    "Expected to find the module in indexed definition."
  where
    perhapsIndexedDefinition
        :: Either
            (Error VerifyError)
            (Map.Map
                ModuleName
                (VerifiedModule Attribute.Symbol Attribute.Axiom)
            )
    perhapsIndexedDefinition =
        verifyAndIndexDefinition
            DoNotVerifyAttributes  -- TODO: Verify attributes.
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

smtlib :: Text -> Attribute
smtlib value = Attribute (Smtlib.smtlibAttribute value)

hook :: Text -> Attribute
hook value = Attribute (Hook.hookAttribute value)

makeSort :: Text -> Sort Object
makeSort name =
    SortActualSort SortActual
        { sortActualName  = testId name
        , sortActualSorts = []
        }

emptyModule :: Text -> Module sentence
emptyModule name =
    Module
        { moduleName = ModuleName name
        , moduleSentences = []
        , moduleAttributes = Attributes []
        }

sortDeclaration :: Text -> KoreSentence
sortDeclaration name =
    asSentence
        (SentenceSort
            { sentenceSortName = testId name
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }
        :: SentenceSort Object CommonKorePattern
        )

symbolDeclaration :: Text -> Text -> [Text] -> KoreSentence
symbolDeclaration name sortName argumentSortNames =
    asSentence
        (SentenceSymbol
            { sentenceSymbolSymbol     = makeSymbol name
            , sentenceSymbolSorts      = map makeSort argumentSortNames
            , sentenceSymbolResultSort = makeSort sortName
            , sentenceSymbolAttributes = Attributes []
            }
        :: SentenceSymbol Object CommonKorePattern
        )

makeSymbol :: Text -> Symbol Object
makeSymbol name =
    Symbol
        { symbolConstructor = testId name
        , symbolParams      = []
        }
