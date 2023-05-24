{- |
Module      : Kore.Rewrite.SMT.Representation.Symbols
Description : Builds an SMT representation for symbols.
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Representation.Symbols (
    buildRepresentations,
) where

import Data.Map.Strict qualified as Map
import Kore.Attribute.Constructor qualified as Attribute (
    Constructor (Constructor, isConstructor),
 )
import Kore.Attribute.Smtlib.Smthook qualified as Attribute (
    Smthook (Smthook, getSmthook),
 )
import Kore.Attribute.Smtlib.Smtlib qualified as Attribute (
    Smtlib (Smtlib, getSmtlib),
 )
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.Attribute.Symbol qualified as Attribute.Symbol (
    Symbol (..),
 )
import Kore.Attribute.Total qualified as Attribute (
    Total (..),
 )
import Kore.IndexedModule.IndexedModule (
    IndexedModule,
    recursiveIndexedModuleSymbolSentences,
 )
import Kore.Rewrite.SMT.AST qualified as AST
import Kore.Syntax.Id (
    Id,
 )
import Kore.Syntax.Sentence (
    SentenceSymbol (SentenceSymbol, sentenceSymbolResultSort, sentenceSymbolSorts, sentenceSymbolSymbol),
 )
import Kore.Syntax.Sentence qualified as Sentence (
    Symbol (Symbol),
 )
import Kore.Syntax.Sentence qualified as Sentence.Symbol (
    Symbol (..),
 )
import Kore.Verified qualified as Verified
import Prelude.Kore
import SMT qualified

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
                    { symbolData = smtName
                    , symbolDeclaration =
                        AST.SymbolBuiltin
                            AST.IndirectSymbolDeclaration
                                { name = AST.AlreadyEncoded smtName
                                , sortDependencies =
                                    AST.SortReference
                                        <$> sentenceSymbolResultSort
                                            : sentenceSymbolSorts
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
                    { symbolData = smtName
                    , symbolDeclaration =
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
        if isConstructor && isDeclaredTotal
            then
                return
                    ( symbolConstructor
                    , AST.Symbol
                        { symbolData = AST.encode encodedName
                        , symbolDeclaration =
                            AST.SymbolConstructor
                                AST.IndirectSymbolDeclaration
                                    { name = encodedName
                                    , sortDependencies =
                                        AST.SortReference
                                            <$> sentenceSymbolResultSort
                                                : sentenceSymbolSorts
                                    }
                        }
                    )
            else Nothing
      where
        Attribute.Constructor{isConstructor} =
            Attribute.Symbol.constructor attributes
        Attribute.Total{isDeclaredTotal} =
            Attribute.Symbol.total attributes
        encodedName = AST.encodable symbolConstructor
