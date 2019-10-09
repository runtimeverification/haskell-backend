module Test.Kore.With
    ( With (..)
    , Attribute (..)
    , ConcreteElement (..)
    , OpaqueSet (..)
    , VariableElement (..)
    ) where

import Data.List
    ( foldl'
    )
import qualified Data.List as List
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )
import qualified Data.List.NonEmpty as NonEmpty
    ( cons
    , reverse
    )
import qualified Data.Map.Strict as Map

import Kore.Attribute.Attributes
    ( AttributePattern
    )
import qualified Kore.Attribute.Sort.Constructors as Attribute
    ( Constructors (Constructors)
    )
import qualified Kore.Attribute.Sort.Constructors as Attribute.Constructors
    ( Constructor (Constructor)
    , ConstructorLike (..)
    )
import qualified Kore.Attribute.Sort.Constructors as Attribute.Constructors.Constructor
    ( Constructor (..)
    )
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Sort as Kore
    ( Sort
    )
import qualified Kore.Step.SMT.AST as AST
    ( Declarations (Declarations)
    , IndirectSymbolDeclaration (IndirectSymbolDeclaration)
    , KoreSortDeclaration (..)
    , KoreSymbolDeclaration (..)
    , Sort (Sort)
    , SortReference (SortReference)
    , Symbol (Symbol)
    , UnresolvedIndirectSymbolDeclaration
    , UnresolvedKoreSymbolDeclaration
    , UnresolvedSymbol
    )
import qualified Kore.Step.SMT.AST as AST.Declarations
    ( Declarations (..)
    )
import qualified Kore.Step.SMT.AST as AST.Sort
    ( Sort (..)
    )
import qualified Kore.Step.SMT.AST as AST.Symbol
    ( Symbol (..)
    )
import qualified Kore.Step.SMT.AST as AST.IndirectSymbolDeclaration
    ( IndirectSymbolDeclaration (..)
    )
import Kore.Syntax.Definition
    ( Attributes (Attributes)
    , Definition (Definition)
    , Module (Module)
    , Sentence (SentenceAliasSentence, SentenceAxiomSentence, SentenceClaimSentence, SentenceHookSentence, SentenceImportSentence, SentenceSortSentence, SentenceSymbolSentence)
    , SentenceAlias (SentenceAlias)
    , SentenceAxiom (SentenceAxiom)
    , SentenceHook (SentenceHookedSort, SentenceHookedSymbol)
    , SentenceImport (SentenceImport)
    , SentenceSort (SentenceSort)
    , SentenceSymbol (SentenceSymbol)
    )
import qualified Kore.Syntax.Definition as Definition
    ( Definition (..)
    )
import qualified Kore.Syntax.Id as Kore
    ( Id
    )
import qualified Kore.Syntax.Module as Module
    ( Module (..)
    )
import Kore.Syntax.Sentence
import qualified Kore.Syntax.Sentence as SentenceAxiom
    ( SentenceAxiom (..)
    )
import qualified Kore.Syntax.Sentence as SentenceAlias
    ( SentenceAlias (..)
    )
import qualified Kore.Syntax.Sentence as SentenceImport
    ( SentenceImport (..)
    )
import qualified Kore.Syntax.Sentence as SentenceSort
    ( SentenceSort (..)
    )
import qualified Kore.Syntax.Sentence as SentenceSymbol
    ( SentenceSymbol (..)
    )
import Kore.Syntax.Variable
    ( Concrete
    )
import qualified SMT.AST as AST
    ( Constructor (Constructor)
    , ConstructorArgument
    , DataTypeDeclaration (DataTypeDeclaration)
    )
import qualified SMT.AST as AST.DataTypeDeclaration
    ( DataTypeDeclaration (..)
    )
import qualified SMT.AST as AST.Constructor
    ( Constructor (..)
    )

class With a b where
    with :: a -> b -> a

newtype Attribute = Attribute { getAttribute :: AttributePattern }

instance (With b c) => With (a->b) (a->c) where
    with fb fc = \a -> fb a `with` fc a

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

instance With (Sentence patt) Attribute where
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

instance With (Sentence patt) [Attribute] where
    with = foldl' with

instance With (SentenceAlias patt) Attribute where
    s@SentenceAlias {sentenceAliasAttributes} `with` attribute =
        s
            { SentenceAlias.sentenceAliasAttributes =
                sentenceAliasAttributes `with` attribute
            }

instance With (SentenceAlias patt) [Attribute] where
    with = foldl' with

instance With (SentenceAxiom patt) Attribute where
    s@SentenceAxiom {sentenceAxiomAttributes} `with` attribute =
        s
            { SentenceAxiom.sentenceAxiomAttributes =
                sentenceAxiomAttributes `with` attribute
            }

instance With (SentenceAxiom patt) [Attribute] where
    with = foldl' with

instance With (SentenceClaim patt) Attribute where
    with a b = SentenceClaim (with (getSentenceClaim a) b)

instance With (SentenceClaim patt) [Attribute] where
    with a b = SentenceClaim (with (getSentenceClaim a) b)

instance With (SentenceImport patt) Attribute where
    s@SentenceImport {sentenceImportAttributes} `with` attribute =
        s
            { SentenceImport.sentenceImportAttributes =
                sentenceImportAttributes `with` attribute
            }

instance With (SentenceImport patt) [Attribute] where
    with = foldl' with

instance With (SentenceSymbol patt) Attribute where
    s@SentenceSymbol {sentenceSymbolAttributes} `with` attribute =
        s
            { SentenceSymbol.sentenceSymbolAttributes =
                sentenceSymbolAttributes `with` attribute
            }

instance With (SentenceSymbol patt) [Attribute] where
    with = foldl' with

instance With (SentenceSort patt) Attribute where
    s@SentenceSort {sentenceSortAttributes} `with` attribute =
        s
            { SentenceSort.sentenceSortAttributes =
                sentenceSortAttributes `with` attribute
            }

instance With (SentenceSort patt) [Attribute] where
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
    (Kore.Id, AST.Sort sort symbol name)
  where
    with
        d@AST.Declarations {sorts}
        (sortId, sort)
      = d { AST.Declarations.sorts = Map.insert sortId sort sorts }

instance With
    (Kore.Id, AST.Sort sort symbol name)
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

instance With (Kore.Id, AST.UnresolvedSymbol) Kore.Sort where
    with (symbolId, symbol) sort = (symbolId, symbol `with` sort)

instance With AST.UnresolvedSymbol Kore.Sort where
    with
        s@AST.Symbol {declaration}
        sort
      = s { AST.Symbol.declaration = declaration `with` sort }

instance With AST.UnresolvedKoreSymbolDeclaration Kore.Sort where
    with (AST.SymbolDeclaredDirectly _) _ =
        error "Cannot add sorts to SymbolDeclaredDirectly."
    with (AST.SymbolBuiltin declaration) sort =
        AST.SymbolBuiltin (declaration `with` sort)
    with (AST.SymbolConstructor declaration) sort =
        AST.SymbolConstructor (declaration `with` sort)

instance With AST.UnresolvedIndirectSymbolDeclaration Kore.Sort where
    with
        s@AST.IndirectSymbolDeclaration {argumentSorts}
        sort
      = s
        { AST.IndirectSymbolDeclaration.argumentSorts =
            argumentSorts `with` AST.SortReference sort
        }

newtype ConcreteElement =
    ConcreteElement {getConcreteElement :: TermLike Concrete}

instance With
    (Domain.NormalizedAc Domain.NormalizedSet (TermLike Concrete) child)
    ConcreteElement
  where
    with
        s@Domain.NormalizedAc {concreteElements}
        (ConcreteElement c)
      | Map.member c concreteElements = error "Duplicated key in set."
      | otherwise = s
        { Domain.concreteElements =
            Map.insert c Domain.SetValue concreteElements
        }

instance With
    (Domain.NormalizedAc Domain.NormalizedSet (TermLike Concrete) child)
    [ConcreteElement]
  where
    with = foldl' with

instance With
    (Domain.NormalizedSet (TermLike Concrete) child)
    ConcreteElement
  where
    with
        (Domain.NormalizedSet ac)
        value
      = Domain.NormalizedSet (ac `with` value)

instance With
    (Domain.NormalizedSet (TermLike Concrete) child)
    [ConcreteElement]
  where
    with = foldl' with

-- VariableElement

newtype VariableElement child = VariableElement {getVariableElement :: child}

instance Ord child
    => With
        (Domain.NormalizedAc Domain.NormalizedSet (TermLike Concrete) child)
        (VariableElement child)
  where
    with
        s@Domain.NormalizedAc {elementsWithVariables}
        (VariableElement v)
      = s
        { Domain.elementsWithVariables =
            List.sort (Domain.SetElement v : elementsWithVariables)
        }

instance Ord child
    => With
        (Domain.NormalizedAc Domain.NormalizedSet (TermLike Concrete) child)
        [VariableElement child]
  where
    with = foldl' with

instance Ord child
    => With
        (Domain.NormalizedSet (TermLike Concrete) child)
        (VariableElement child)
  where
    with
        (Domain.NormalizedSet ac)
        value
      = Domain.NormalizedSet (ac `with` value)

instance Ord child
    => With
        (Domain.NormalizedSet (TermLike Concrete) child)
        [VariableElement child]
  where
    with = foldl' with

-- OpaqueSet

newtype OpaqueSet child = OpaqueSet {getOpaqueSet :: child}

instance Ord child
    => With
        (Domain.NormalizedAc Domain.NormalizedSet (TermLike Concrete) child)
        (OpaqueSet child)
  where
    with
        s@Domain.NormalizedAc {opaque}
        (OpaqueSet v)
      = s
        { Domain.opaque = List.sort (v : opaque) }

instance Ord child
    => With
        (Domain.NormalizedAc Domain.NormalizedSet (TermLike Concrete) child)
        [OpaqueSet child]
  where
    with = foldl' with


instance Ord child
    => With
        (Domain.NormalizedSet (TermLike Concrete) child)
        (OpaqueSet child)
  where
    with
        (Domain.NormalizedSet ac)
        value
      = Domain.NormalizedSet (ac `with` value)

instance Ord child
    => With
        (Domain.NormalizedSet (TermLike Concrete) child)
        [OpaqueSet child]
  where
    with = foldl' with

instance With Attribute.Constructors Attribute.Constructors.ConstructorLike
  where
    with (Attribute.Constructors Nothing) constructorLike =
        Attribute.Constructors (Just (constructorLike :| []))
    with
        (Attribute.Constructors (Just constructors))
        constructorLike
      = Attribute.Constructors
        $ Just
        $ nonEmptyAppend constructorLike constructors

instance With Attribute.Constructors.ConstructorLike Kore.Sort
  where
    with
        (Attribute.Constructors.ConstructorLikeConstructor constructor) sort
      =
        Attribute.Constructors.ConstructorLikeConstructor
            (constructor `with` sort)
    with
        Attribute.Constructors.ConstructorLikeInjection _sort
      =
        error "Cannot add sort to injection."


instance With Attribute.Constructors.Constructor Kore.Sort
  where
    with
        c@(Attribute.Constructors.Constructor {sorts}) sort
      =
        c{Attribute.Constructors.Constructor.sorts = sorts ++ [sort]}

nonEmptyAppend :: a -> NonEmpty a -> NonEmpty a
nonEmptyAppend a = NonEmpty.reverse . NonEmpty.cons a . NonEmpty.reverse
