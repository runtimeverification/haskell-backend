{- |
Module      : Kore.Step.SMT.Representation.Symbols
Description : Builds an SMT representation for symbols.
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Step.SMT.Representation.Symbols (
    buildRepresentations,
) where

import qualified Data.Map.Strict as Map
import qualified Kore.Attribute.Constructor as Attribute (
    Constructor (Constructor, isConstructor),
 )
import qualified Kore.Attribute.Functional as Attribute (
    Functional (Functional, isDeclaredFunctional),
 )
import qualified Kore.Attribute.Smtlib.Smthook as Attribute (
    Smthook (Smthook, getSmthook),
 )
import qualified Kore.Attribute.Smtlib.Smtlib as Attribute (
    Smtlib (Smtlib, getSmtlib),
 )
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Attribute.Symbol as Attribute.Symbol (
    Symbol (..),
 )
import Kore.IndexedModule.IndexedModule (
    IndexedModule,
    recursiveIndexedModuleSymbolSentences,
 )
import qualified Kore.Step.SMT.AST as AST
import Kore.Syntax.Id (
    Id,
 )
import Kore.Syntax.Sentence (
    SentenceSymbol (SentenceSymbol, sentenceSymbolResultSort, sentenceSymbolSorts, sentenceSymbolSymbol),
 )
import qualified Kore.Syntax.Sentence as Sentence (
    Symbol (Symbol),
 )
import qualified Kore.Syntax.Sentence as Sentence.Symbol (
    Symbol (..),
 )
import qualified Kore.Verified as Verified
import Prelude.Kore
import qualified SMT

{- | Builds smt representations for symbols in the given module.

May ignore symbols that we don't handle yet (e.g. non-constructors without smt
related attributes).

All references to other sorts and symbols are left unresolved.
-}
buildRepresentations ::
    forall axiom.
    IndexedModule Verified.Pattern Attribute.Symbol axiom ->
    AST.UnresolvedDeclarations
buildRepresentations indexedModule =
    listToDeclarations builtinDeclarations
        `AST.mergePreferFirst` listToDeclarations constructorDeclarations
        `AST.mergePreferFirst` listToDeclarations smtlibDeclarations
  where
    listToDeclarations ::
        [(Id, AST.UnresolvedSymbol)] ->
        AST.UnresolvedDeclarations
    listToDeclarations list =
        AST.Declarations
            { sorts = Map.empty
            , symbols = Map.fromList list
            }

    extractDefinitionsFromSentences ::
        ( (Attribute.Symbol, Verified.SentenceSymbol) ->
          Maybe (Id, AST.UnresolvedSymbol)
        ) ->
        [(Id, AST.UnresolvedSymbol)]
    extractDefinitionsFromSentences definitionExtractor =
        mapMaybe
            definitionExtractor
            (Map.elems $ recursiveIndexedModuleSymbolSentences indexedModule)

    builtinDeclarations :: [(Id, AST.UnresolvedSymbol)]
    builtinDeclarations =
        extractDefinitionsFromSentences builtinDeclaration

    smtlibDeclarations :: [(Id, AST.UnresolvedSymbol)]
    smtlibDeclarations =
        extractDefinitionsFromSentences smtlibDeclaration

    constructorDeclarations :: [(Id, AST.UnresolvedSymbol)]
    constructorDeclarations =
        extractDefinitionsFromSentences constructorDeclaration

builtinDeclaration ::
    (Attribute.Symbol, Verified.SentenceSymbol) ->
    Maybe (Id, AST.UnresolvedSymbol)
builtinDeclaration
    ( attributes
        , SentenceSymbol
            { sentenceSymbolSymbol = Sentence.Symbol{symbolConstructor}
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            }
        ) =
        do
            smtName <- getSmthook
            return
                ( symbolConstructor
                , AST.Symbol
                    { smtFromSortArgs = const . const $ Just smtName
                    , declaration =
                        AST.SymbolBuiltin
                            AST.IndirectSymbolDeclaration
                                { name = AST.AlreadyEncoded smtName
                                , sortDependencies =
                                    AST.SortReference
                                        <$> sentenceSymbolResultSort :
                                    sentenceSymbolSorts
                                }
                    }
                )
      where
        Attribute.Smthook{getSmthook} = Attribute.Symbol.smthook attributes

smtlibDeclaration ::
    (Attribute.Symbol, Verified.SentenceSymbol) ->
    Maybe (Id, AST.UnresolvedSymbol)
smtlibDeclaration
    ( attributes
        , SentenceSymbol
            { sentenceSymbolSymbol =
                Sentence.Symbol{symbolConstructor}
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            }
        ) =
        do
            smtName <- getSmtlib
            return
                ( symbolConstructor
                , AST.Symbol
                    { smtFromSortArgs = const . const $ Just smtName
                    , declaration =
                        AST.SymbolDeclaredDirectly
                            SMT.FunctionDeclaration
                                { name = AST.AlreadyEncoded smtName
                                , inputSorts = map AST.SortReference sentenceSymbolSorts
                                , resultSort = AST.SortReference sentenceSymbolResultSort
                                }
                    }
                )
      where
        Attribute.Smtlib{getSmtlib} = Attribute.Symbol.smtlib attributes

constructorDeclaration ::
    (Attribute.Symbol, Verified.SentenceSymbol) ->
    Maybe (Id, AST.UnresolvedSymbol)
constructorDeclaration
    ( attributes
        , SentenceSymbol
            { sentenceSymbolSymbol = Sentence.Symbol{symbolConstructor}
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            }
        ) =
        if isConstructor && isDeclaredFunctional
            then
                return
                    ( symbolConstructor
                    , AST.Symbol
                        { smtFromSortArgs =
                            const . const $ Just (AST.encode encodedName)
                        , declaration =
                            AST.SymbolConstructor
                                AST.IndirectSymbolDeclaration
                                    { name = encodedName
                                    , sortDependencies =
                                        AST.SortReference
                                            <$> sentenceSymbolResultSort :
                                        sentenceSymbolSorts
                                    }
                        }
                    )
            else Nothing
      where
        Attribute.Constructor{isConstructor} =
            Attribute.Symbol.constructor attributes
        Attribute.Functional{isDeclaredFunctional} =
            Attribute.Symbol.functional attributes
        encodedName = AST.encodable symbolConstructor
