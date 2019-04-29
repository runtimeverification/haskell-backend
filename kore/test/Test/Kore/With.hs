module Test.Kore.With
    ( With (..)
    , Attribute (..)
    ) where

import           Data.List
                 ( foldl' )
import qualified Data.Map.Strict as Map

import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Sentence
                 ( Attributes (Attributes), Definition (Definition),
                 Module (Module),
                 Sentence (SentenceAliasSentence, SentenceAxiomSentence, SentenceClaimSentence, SentenceHookSentence, SentenceImportSentence, SentenceSortSentence, SentenceSymbolSentence),
                 SentenceAlias (SentenceAlias), SentenceAxiom (SentenceAxiom),
                 SentenceHook (SentenceHookedSort, SentenceHookedSymbol),
                 SentenceImport (SentenceImport), SentenceSort (SentenceSort),
                 SentenceSymbol (SentenceSymbol) )
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
import           Kore.Attribute.Attributes
                 ( AttributePattern )
import qualified Kore.Sort as Kore
                 ( Sort )
import qualified Kore.Step.SMT.AST as AST
                 ( Declarations (Declarations),
                 IndirectSymbolDeclaration (IndirectSymbolDeclaration),
                 KoreSortDeclaration (..), KoreSymbolDeclaration (..),
                 Sort (Sort), SortReference (SortReference), Symbol (Symbol),
                 UnresolvedIndirectSymbolDeclaration,
                 UnresolvedKoreSymbolDeclaration, UnresolvedSymbol )
import qualified Kore.Step.SMT.AST as AST.Declarations
                 ( Declarations (..) )
import qualified Kore.Step.SMT.AST as AST.Sort
                 ( Sort (..) )
import qualified Kore.Step.SMT.AST as AST.Symbol
                 ( Symbol (..) )
import qualified Kore.Step.SMT.AST as AST.IndirectSymbolDeclaration
                 ( IndirectSymbolDeclaration (..) )
import qualified Kore.Syntax.Id as Kore
                 ( Id )
import qualified SMT.AST as AST
                 ( Constructor (Constructor), ConstructorArgument,
                 DataTypeDeclaration (DataTypeDeclaration) )
import qualified SMT.AST as AST.DataTypeDeclaration
                 ( DataTypeDeclaration (..) )
import qualified SMT.AST as AST.Constructor
                 ( Constructor (..) )

class With a b where
    with :: a -> b -> a

newtype Attribute = Attribute { getAttribute :: AttributePattern }

instance With [a] a where
    with as a = a : as

instance With (Module sentence) Attribute where
    with
        m@Module {moduleAttributes = Attributes as}
        Attribute {getAttribute}
      = m { Module.moduleAttributes = Attributes (as `with` getAttribute) }

instance With (Module sentence) [Attribute] where
    with = foldl' with

instance With (Definition sentence) Attribute where
    with
        d@Definition {definitionAttributes = Attributes as}
        Attribute {getAttribute}
      = d
        { Definition.definitionAttributes = Attributes (as `with` getAttribute)
        }

instance With (Definition sentence) [Attribute] where
    with = foldl' with

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

instance With (Sentence level sort patt) [Attribute] where
    with = foldl' with

instance With (SentenceAlias level patt) Attribute where
    s@SentenceAlias {sentenceAliasAttributes} `with` attribute =
        s
            { SentenceAlias.sentenceAliasAttributes =
                sentenceAliasAttributes `with` attribute
            }

instance With (SentenceAlias level patt) [Attribute] where
    with = foldl' with

instance With (SentenceAxiom sort patt) Attribute where
    s@SentenceAxiom {sentenceAxiomAttributes} `with` attribute =
        s
            { SentenceAxiom.sentenceAxiomAttributes =
                sentenceAxiomAttributes `with` attribute
            }

instance With (SentenceAxiom sort patt) [Attribute] where
    with = foldl' with

instance With (SentenceImport patt) Attribute where
    s@SentenceImport {sentenceImportAttributes} `with` attribute =
        s
            { SentenceImport.sentenceImportAttributes =
                sentenceImportAttributes `with` attribute
            }

instance With (SentenceImport patt) [Attribute] where
    with = foldl' with

instance With (SentenceSymbol level patt) Attribute where
    s@SentenceSymbol {sentenceSymbolAttributes} `with` attribute =
        s
            { SentenceSymbol.sentenceSymbolAttributes =
                sentenceSymbolAttributes `with` attribute
            }

instance With (SentenceSymbol level patt) [Attribute] where
    with = foldl' with

instance With (SentenceSort level patt) Attribute where
    s@SentenceSort {sentenceSortAttributes} `with` attribute =
        s
            { SentenceSort.sentenceSortAttributes =
                sentenceSortAttributes `with` attribute
            }

instance With (SentenceSort level patt) [Attribute] where
    with = foldl' with

instance With Attributes Attribute where
    (Attributes attributes) `with` Attribute {getAttribute} =
        Attributes (attributes `with` getAttribute)

instance With Attributes [Attribute] where
    with = foldl' with

instance With (Module sentence) sentence where
    with
        m@Module {moduleSentences = sentences}
        sentence
      = m { Module.moduleSentences = sentences `with` sentence }

instance With
    (AST.Declarations sort symbol name)
    (Kore.Id Object, AST.Sort sort symbol name)
  where
    with
        d@AST.Declarations {sorts}
        (sortId, sort)
      = d { AST.Declarations.sorts = Map.insert sortId sort sorts }

instance With
    (Kore.Id Object, AST.Sort sort symbol name)
    (AST.Constructor sort symbol name)
  where
    with (sortId, sort) constructor = (sortId, sort `with` constructor)

instance With (AST.Sort sort symbol name) (AST.Constructor sort symbol name)
  where
    with
        s@AST.Sort {declaration}
        constructor
      = s { AST.Sort.declaration = declaration `with` constructor }

instance With
    (AST.KoreSortDeclaration sort symbol name)
    (AST.Constructor sort symbol name)
  where
    with
        (AST.SortDeclarationDataType declaration)
        constructor
      = AST.SortDeclarationDataType (declaration `with` constructor)
    with (AST.SortDeclarationSort _) _ =
        error "Cannot add constructors to SortDeclarationSort."
    with (AST.SortDeclaredIndirectly _) _ =
        error "Cannot add constructors to SortDeclaredIndirectly."

instance With
    (AST.DataTypeDeclaration sort symbol name)
    (AST.Constructor sort symbol name)
  where
    with
        s@AST.DataTypeDeclaration {constructors}
        constructor
      = s
            { AST.DataTypeDeclaration.constructors =
                constructors `with` constructor
            }

instance With
    (AST.Constructor sort symbol name)
    (AST.ConstructorArgument sort name)
  where
    with
        s@AST.Constructor {arguments}
        argument
      = s
            { AST.Constructor.arguments = arguments `with` argument
            }

instance With
    (Kore.Id Object, AST.UnresolvedSymbol)
    (Kore.Sort Object)
  where
    with (symbolId, symbol) sort = (symbolId, symbol `with` sort)

instance With AST.UnresolvedSymbol (Kore.Sort Object)
  where
    with
        s@AST.Symbol {declaration}
        sort
      = s { AST.Symbol.declaration = declaration `with` sort }

instance With AST.UnresolvedKoreSymbolDeclaration (Kore.Sort Object)
  where
    with (AST.SymbolDeclaredDirectly _) _ =
        error "Cannot add sorts to SymbolDeclaredDirectly."
    with (AST.SymbolDeclaredIndirectly declaration) sort =
        AST.SymbolDeclaredIndirectly (declaration `with` sort)

instance With AST.UnresolvedIndirectSymbolDeclaration (Kore.Sort Object)
  where
    with
        s@AST.IndirectSymbolDeclaration {sorts}
        sort
      = s
        { AST.IndirectSymbolDeclaration.sorts =
            sorts `with` AST.SortReference sort
        }
