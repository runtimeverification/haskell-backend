module Test.Kore.With (
    With (..),
    Attribute (..),
    OpaqueSet (..),
    VariableElement (..),
) where

import Control.Lens qualified as Lens
import Data.Generics.Product (
    field,
 )
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.List qualified as List
import Data.List.NonEmpty qualified as NonEmpty (
    cons,
    reverse,
 )
import Data.Map.Strict qualified as Map
import Kore.Attribute.Sort.Constructors qualified as Attribute (
    Constructors (Constructors),
 )
import Kore.Attribute.Sort.Constructors qualified as Attribute.Constructors (
    Constructor (Constructor),
    ConstructorLike (..),
 )
import Kore.Attribute.Sort.Constructors qualified as Attribute.Constructors.Constructor (
    Constructor (..),
 )
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.TermLike (
    Key,
 )
import Kore.Rewrite.SMT.AST qualified as AST (
    Declarations (Declarations),
    IndirectSymbolDeclaration (IndirectSymbolDeclaration),
    KoreSortDeclaration (..),
    KoreSymbolDeclaration (..),
    Sort (Sort),
    SortReference (SortReference),
    Symbol (Symbol),
    UnresolvedIndirectSymbolDeclaration,
    UnresolvedKoreSymbolDeclaration,
    UnresolvedSymbol,
 )
import Kore.Rewrite.SMT.AST qualified as AST.Declarations (
    Declarations (..),
 )
import Kore.Rewrite.SMT.AST qualified as AST.IndirectSymbolDeclaration (
    IndirectSymbolDeclaration (..),
 )
import Kore.Rewrite.SMT.AST qualified as AST.Sort (
    Sort (..),
 )
import Kore.Rewrite.SMT.AST qualified as AST.Symbol (
    Symbol (..),
 )
import Kore.Sort qualified as Kore (
    Sort,
 )
import Kore.Syntax.Definition (
    Definition (Definition),
 )
import Kore.Syntax.Definition qualified as Definition (
    Definition (..),
 )
import Kore.Syntax.Id qualified as Kore (
    Id,
 )
import Kore.Syntax.Module qualified as Module (
    Module (..),
 )
import Kore.Syntax.Sentence
import Kore.Syntax.Sentence qualified as SentenceAlias (
    SentenceAlias (..),
 )
import Kore.Syntax.Sentence qualified as SentenceAxiom (
    SentenceAxiom (..),
 )
import Kore.Syntax.Sentence qualified as SentenceImport (
    SentenceImport (..),
 )
import Kore.Syntax.Sentence qualified as SentenceSort (
    SentenceSort (..),
 )
import Kore.Syntax.Sentence qualified as SentenceSymbol (
    SentenceSymbol (..),
 )
import Prelude.Kore
import SMT.AST qualified as AST (
    Constructor (Constructor),
    ConstructorArgument,
    DataTypeDeclaration (DataTypeDeclaration),
 )
import SMT.AST qualified as AST.Constructor (
    Constructor (..),
 )
import SMT.AST qualified as AST.DataTypeDeclaration (
    DataTypeDeclaration (..),
 )

class With a b where
    with :: a -> b -> a

newtype Attribute = Attribute {getAttribute :: AttributePattern}

instance (With b c) => With (a -> b) (a -> c) where
    with fb fc = \a -> fb a `with` fc a

instance With [a] a where
    with as a = a : as

instance With (Module sentence) Attribute where
    with
        m@Module{moduleAttributes = Attributes as}
        Attribute{getAttribute} =
            m{Module.moduleAttributes = Attributes (as `with` getAttribute)}

instance With (Module sentence) [Attribute] where
    with = foldl' with

instance With (Definition sentence) Attribute where
    with
        d@Definition{definitionAttributes = Attributes as}
        Attribute{getAttribute} =
            d
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
    s@SentenceAlias{sentenceAliasAttributes} `with` attribute =
        s
            { SentenceAlias.sentenceAliasAttributes =
                sentenceAliasAttributes `with` attribute
            }

instance With (SentenceAlias patt) [Attribute] where
    with = foldl' with

instance With (SentenceAxiom patt) Attribute where
    s@SentenceAxiom{sentenceAxiomAttributes} `with` attribute =
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

instance With SentenceImport Attribute where
    s@SentenceImport{sentenceImportAttributes} `with` attribute =
        s
            { SentenceImport.sentenceImportAttributes =
                sentenceImportAttributes `with` attribute
            }

instance With SentenceImport [Attribute] where
    with = foldl' with

instance With SentenceSymbol Attribute where
    s@SentenceSymbol{sentenceSymbolAttributes} `with` attribute =
        s
            { SentenceSymbol.sentenceSymbolAttributes =
                sentenceSymbolAttributes `with` attribute
            }

instance With SentenceSymbol [Attribute] where
    with = foldl' with

instance With SentenceSort Attribute where
    s@SentenceSort{sentenceSortAttributes} `with` attribute =
        s
            { SentenceSort.sentenceSortAttributes =
                sentenceSortAttributes `with` attribute
            }

instance With SentenceSort [Attribute] where
    with = foldl' with

instance With Attributes Attribute where
    (Attributes attributes) `with` Attribute{getAttribute} =
        Attributes (attributes `with` getAttribute)

instance With Attributes [Attribute] where
    with = foldl' with

instance With (Module sentence) sentence where
    with
        m@Module{moduleSentences = sentences}
        sentence =
            m{Module.moduleSentences = sentences `with` sentence}

instance
    With
        (AST.Declarations sort symbol name)
        (Kore.Id, AST.Sort sort symbol name)
    where
    with
        d@AST.Declarations{sorts}
        (sortId, sort) =
            d{AST.Declarations.sorts = Map.insert sortId sort sorts}

instance
    With
        (Kore.Id, AST.Sort sort symbol name)
        (AST.Constructor sort symbol name)
    where
    with (sortId, sort) constructor = (sortId, sort `with` constructor)

instance With (AST.Sort sort symbol name) (AST.Constructor sort symbol name) where
    with
        s@AST.Sort{sortDeclaration}
        constructor =
            s{AST.Sort.sortDeclaration = sortDeclaration `with` constructor}

instance
    With
        (AST.KoreSortDeclaration sort symbol name)
        (AST.Constructor sort symbol name)
    where
    with
        (AST.SortDeclarationDataType declaration)
        constructor =
            AST.SortDeclarationDataType (declaration `with` constructor)
    with (AST.SortDeclarationSort _) _ =
        error "Cannot add constructors to SortDeclarationSort."
    with (AST.SortDeclaredIndirectly _) _ =
        error "Cannot add constructors to SortDeclaredIndirectly."

instance
    With
        (AST.DataTypeDeclaration sort symbol name)
        (AST.Constructor sort symbol name)
    where
    with
        s@AST.DataTypeDeclaration{constructors}
        constructor =
            s
                { AST.DataTypeDeclaration.constructors =
                    constructors `with` constructor
                }

instance
    With
        (AST.Constructor sort symbol name)
        (AST.ConstructorArgument sort name)
    where
    with
        s@AST.Constructor{arguments}
        argument =
            s
                { AST.Constructor.arguments = arguments `with` argument
                }

instance With (Kore.Id, AST.UnresolvedSymbol) Kore.Sort where
    with (symbolId, symbol) sort = (symbolId, symbol `with` sort)

instance With AST.UnresolvedSymbol Kore.Sort where
    with
        s@AST.Symbol{symbolDeclaration}
        sort =
            s{AST.Symbol.symbolDeclaration = symbolDeclaration `with` sort}

instance With AST.UnresolvedKoreSymbolDeclaration Kore.Sort where
    with (AST.SymbolDeclaredDirectly _) _ =
        error "Cannot add sorts to SymbolDeclaredDirectly."
    with (AST.SymbolBuiltin declaration) sort =
        AST.SymbolBuiltin (declaration `with` sort)
    with (AST.SymbolConstructor declaration) sort =
        AST.SymbolConstructor (declaration `with` sort)

instance With AST.UnresolvedIndirectSymbolDeclaration Kore.Sort where
    with
        s@AST.IndirectSymbolDeclaration{sortDependencies}
        sort =
            s
                { AST.IndirectSymbolDeclaration.sortDependencies =
                    sortDependencies `with` AST.SortReference sort
                }

instance
    With
        (NormalizedAc NormalizedSet Key child)
        Key
    where
    with
        s@NormalizedAc{concreteElements}
        key
            | HashMap.member key concreteElements =
                error "Duplicated key in set."
            | otherwise =
                s
                    { concreteElements =
                        HashMap.insert key SetValue concreteElements
                    }

instance
    With
        (NormalizedAc NormalizedSet Key child)
        [Key]
    where
    with = foldl' with

instance
    With
        (NormalizedSet Key child)
        Key
    where
    with
        (NormalizedSet ac)
        value =
            NormalizedSet (ac `with` value)

instance
    With
        (NormalizedSet Key child)
        [Key]
    where
    with = foldl' with

-- VariableElement

newtype VariableElement child = VariableElement {getVariableElement :: child}

instance
    (Hashable child, Ord child) =>
    With
        (NormalizedAc NormalizedSet Key child)
        (VariableElement child)
    where
    with
        internalSet
        (VariableElement v) =
            Lens.over
                (field @"elementsWithVariables")
                ( \symbolicVariables ->
                    let newElement = SetElement v
                        newSymbolicVariables =
                            newElement : symbolicVariables
                        simulateNormalize = HashSet.toList . HashSet.fromList
                     in if newElement `elem` symbolicVariables
                            then -- user intended for a de-normalized internalSet
                                newSymbolicVariables
                            else -- this simulates the reordering of the elements
                            -- which happens during AC normalization
                                simulateNormalize newSymbolicVariables
                )
                internalSet

instance
    (Hashable child, Ord child) =>
    With
        (NormalizedAc NormalizedSet Key child)
        [VariableElement child]
    where
    with = foldl' with

instance
    (Hashable child, Ord child) =>
    With
        (NormalizedSet Key child)
        (VariableElement child)
    where
    with
        (NormalizedSet ac)
        value =
            NormalizedSet (ac `with` value)

instance
    (Hashable child, Ord child) =>
    With
        (NormalizedSet Key child)
        [VariableElement child]
    where
    with = foldl' with

-- OpaqueSet

newtype OpaqueSet child = OpaqueSet {getOpaqueSet :: child}

instance
    Ord child =>
    With
        (NormalizedAc NormalizedSet Key child)
        (OpaqueSet child)
    where
    with
        s@NormalizedAc{opaque}
        (OpaqueSet v) =
            s
                { opaque = List.sort (v : opaque)
                }

instance
    Ord child =>
    With
        (NormalizedAc NormalizedSet Key child)
        [OpaqueSet child]
    where
    with = foldl' with

instance
    Ord child =>
    With
        (NormalizedSet Key child)
        (OpaqueSet child)
    where
    with
        (NormalizedSet ac)
        value =
            NormalizedSet (ac `with` value)

instance
    Ord child =>
    With
        (NormalizedSet Key child)
        [OpaqueSet child]
    where
    with = foldl' with

instance With Attribute.Constructors Attribute.Constructors.ConstructorLike where
    with (Attribute.Constructors Nothing) constructorLike =
        Attribute.Constructors (Just (constructorLike :| []))
    with
        (Attribute.Constructors (Just constructors))
        constructorLike =
            Attribute.Constructors $
                Just $
                    nonEmptyAppend constructorLike constructors

instance With Attribute.Constructors.ConstructorLike Kore.Sort where
    with
        (Attribute.Constructors.ConstructorLikeConstructor constructor)
        sort =
            Attribute.Constructors.ConstructorLikeConstructor
                (constructor `with` sort)
    with
        Attribute.Constructors.ConstructorLikeInjection
        _sort =
            error "Cannot add sort to injection."

instance With Attribute.Constructors.Constructor Kore.Sort where
    with
        c@Attribute.Constructors.Constructor{sorts}
        sort =
            c{Attribute.Constructors.Constructor.sorts = sorts ++ [sort]}

nonEmptyAppend :: a -> NonEmpty a -> NonEmpty a
nonEmptyAppend a = NonEmpty.reverse . NonEmpty.cons a . NonEmpty.reverse
