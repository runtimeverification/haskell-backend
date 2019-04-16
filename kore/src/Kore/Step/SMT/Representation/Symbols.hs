{-|
Module      : Kore.Step.SMT.Representation.Symbols
Description : Builds an SMT representation for symbols.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Representation.Symbols
    ( buildRepresentations
    ) where

import qualified Data.Map as Map
import           Data.Maybe
                 ( mapMaybe )
import           Data.Text
                 ( Text )

import           Kore.AST.Identifier
                 ( Id )
import           Kore.AST.Kore
                 ( VerifiedKorePattern )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Sentence
                 ( SentenceSymbol (SentenceSymbol, sentenceSymbolResultSort, sentenceSymbolSorts, sentenceSymbolSymbol) )
import qualified Kore.AST.Sentence as Sentence
                 ( Symbol (Symbol) )
import qualified Kore.AST.Sentence as Sentence.Symbol
                 ( Symbol (..) )
import qualified Kore.Attribute.Constructor as Attribute
                 ( Constructor (Constructor, isConstructor) )
import qualified Kore.Attribute.Functional as Attribute
                 ( Functional (Functional, isDeclaredFunctional) )
import qualified Kore.Attribute.Smtlib.Smthook as Attribute
                 ( Smthook (Smthook, getSmthook) )
import qualified Kore.Attribute.Smtlib.Smtlib as Attribute
                 ( Smtlib (Smtlib, getSmtlib) )
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import qualified Kore.Attribute.Symbol as Attribute.Symbol
                 ( Symbol (..) )
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule, recursiveIndexedModuleSymbolSentences )
import           Kore.Sort
                 ( Sort )
import qualified Kore.Step.SMT.AST as AST
import           Kore.Unparser
                 ( unparseToString )
import qualified SMT

nameFromSExpression :: SMT.SExpr -> Text
nameFromSExpression (SMT.Atom name) = name
nameFromSExpression (SMT.List (SMT.Atom name : _)) = name
nameFromSExpression e =
    (error . unlines)
        [ "Cannot extract name from s-expression."
        , "expression=" ++ SMT.showSExpr e
        ]

{-| Builds smt representations for symbols in the given module.

May ignore symbols that we don't handle yet (e.g. non-constructors without smt
related attributes).

All references to other sorts and symbols are left unresolved.
-}
buildRepresentations
    :: forall indexedModule param axiom
    .   ( indexedModule ~
            IndexedModule
                param
                VerifiedKorePattern
                Attribute.Symbol
                axiom
        )
    => indexedModule
    -> AST.UnresolvedDeclarations
buildRepresentations indexedModule =
    listToDeclarations builtinDeclarations
    `AST.mergePreferFirst` listToDeclarations smtlibDeclarations
    `AST.mergePreferFirst` listToDeclarations constructorDeclarations
  where
    listToDeclarations
        :: [(Id Object, AST.UnresolvedSymbol)]
        -> AST.UnresolvedDeclarations
    listToDeclarations list =
        AST.Declarations
            { sorts = Map.empty
            , symbols = Map.fromList list
            }

    extractDefinitionsFromSentences
        ::  (   ( Attribute.Symbol
                , SentenceSymbol Object VerifiedKorePattern
                )
            -> Maybe (Id Object, AST.UnresolvedSymbol)
            )
        -> [(Id Object, AST.UnresolvedSymbol)]
    extractDefinitionsFromSentences definitionExtractor =
        mapMaybe
            definitionExtractor
            (Map.elems $ recursiveIndexedModuleSymbolSentences indexedModule)

    builtinDeclarations :: [(Id Object, AST.UnresolvedSymbol)]
    builtinDeclarations =
        extractDefinitionsFromSentences builtinDeclaration

    smtlibDeclarations :: [(Id Object, AST.UnresolvedSymbol)]
    smtlibDeclarations =
        extractDefinitionsFromSentences smtlibDeclaration

    constructorDeclarations :: [(Id Object, AST.UnresolvedSymbol)]
    constructorDeclarations =
        extractDefinitionsFromSentences constructorDeclaration

builtinDeclaration
    ::  ( Attribute.Symbol
        , SentenceSymbol Object VerifiedKorePattern
        )
    -> Maybe (Id Object, AST.UnresolvedSymbol)
builtinDeclaration
    ( attributes
    , SentenceSymbol
        { sentenceSymbolSymbol = Sentence.Symbol { symbolConstructor }
        , sentenceSymbolSorts
        , sentenceSymbolResultSort
        }
    )
  = do
    smtName <- nameFromSExpression <$> getSmthook
    return
        ( symbolConstructor
        , AST.Symbol
            { smtFromSortArgs = emptySortArgsToSmt (SMT.Atom smtName)
            , declaration =
                AST.SymbolDeclaredIndirectly
                    (map
                        AST.SortReference
                        (sentenceSymbolResultSort : sentenceSymbolSorts)
                    )
            }
        )
  where
    Attribute.Smthook {getSmthook} = Attribute.Symbol.smthook attributes

smtlibDeclaration
    ::  ( Attribute.Symbol
        , SentenceSymbol Object VerifiedKorePattern
        )
    -> Maybe (Id Object, AST.UnresolvedSymbol)
smtlibDeclaration
    ( attributes
    , SentenceSymbol
        { sentenceSymbolSymbol =
            Sentence.Symbol { symbolConstructor }
        , sentenceSymbolSorts
        , sentenceSymbolResultSort
        }
    )
  = do
    smtName <- nameFromSExpression <$> getSmtlib
    return
        ( symbolConstructor
        , AST.Symbol
            { smtFromSortArgs = emptySortArgsToSmt (SMT.Atom smtName)
            , declaration = AST.SymbolDeclaredDirectly
                SMT.FunctionDeclaration
                    { name = AST.AlreadyEncoded smtName
                    , inputSorts = map AST.SortReference sentenceSymbolSorts
                    , resultSort = AST.SortReference sentenceSymbolResultSort
                    }
            }
        )
  where
    Attribute.Smtlib { getSmtlib } = Attribute.Symbol.smtlib attributes

constructorDeclaration
    ::  ( Attribute.Symbol
        , SentenceSymbol Object VerifiedKorePattern
        )
    -> Maybe (Id Object, AST.UnresolvedSymbol)
constructorDeclaration
    ( attributes
    , SentenceSymbol
        { sentenceSymbolSymbol = Sentence.Symbol { symbolConstructor }
        , sentenceSymbolSorts
        , sentenceSymbolResultSort
        }
    )
  = if isConstructor && isDeclaredFunctional
    then return
        ( symbolConstructor
        , AST.Symbol
            { smtFromSortArgs =
                emptySortArgsToSmt (SMT.Atom $ AST.encode encodedName)
            , declaration =
                AST.SymbolDeclaredIndirectly
                    (map
                        AST.SortReference
                        (sentenceSymbolResultSort : sentenceSymbolSorts)
                    )
            }
        )
    else Nothing
  where
    Attribute.Constructor { isConstructor } =
        Attribute.Symbol.constructor attributes
    Attribute.Functional { isDeclaredFunctional } =
        Attribute.Symbol.functional attributes
    encodedName = AST.encodable symbolConstructor

emptySortArgsToSmt
    :: SMT.SExpr
    -> Map.Map (Id Object) AST.SmtSort
    -> [Sort Object]
    -> Maybe SMT.SExpr
emptySortArgsToSmt representation _ [] = Just representation
emptySortArgsToSmt representation _ args = (error . unlines)
    [ "Symbols with arguments not supported yet."
    , "representation=" ++ SMT.showSExpr representation
    , "args = " ++ show (fmap unparseToString args)
    ]
