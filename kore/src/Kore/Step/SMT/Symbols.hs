{-|
Module      : Kore.Step.SMT.Symbols
Description : Declares symbols to the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}

module Kore.Step.SMT.Symbols
    ( SymbolTranslation (..)
    , declareSymbols
    , translateSymbol
    ) where

import Data.Reflection
       ( Given, given )
import Data.Text
       ( Text )

import           Kore.AST.Common
                 ( SymbolOrAlias (SymbolOrAlias), Variable )
import           Kore.AST.Common as SymbolOrAlias
                 ( SymbolOrAlias (..) )
import           Kore.AST.Identifier
                 ( Id (getId) )
import           Kore.AST.Kore
                 ( KorePattern )
import           Kore.AST.MetaOrObject
                 ( Object, Unified )
import           Kore.AST.Sentence
                 ( SentenceSymbol (SentenceSymbol, sentenceSymbolSymbol) )
import qualified Kore.AST.Sentence as Sentence
                 ( Symbol (Symbol) )
import qualified Kore.AST.Sentence as Sentence.Symbol
                 ( Symbol (..) )
import           Kore.AST.Valid
                 ( Valid )
import           Kore.ASTHelpers
                 ( ApplicationSorts (ApplicationSorts) )
import qualified Kore.ASTHelpers as ApplicationSorts
                 ( ApplicationSorts (..) )
import qualified Kore.Attribute.Axiom as Attribute
                 ( Axiom )
import qualified Kore.Attribute.Constructor as Attribute
                 ( Constructor (Constructor, isConstructor) )
import qualified Kore.Attribute.Smtlib.Smthook as Attribute
                 ( Smthook (Smthook, getSmthook) )
import qualified Kore.Attribute.Smtlib.Smtlib as Attribute
                 ( Smtlib (Smtlib, getSmtlib) )
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol (Symbol) )
import qualified Kore.Attribute.Symbol as Attribute.Symbol
                 ( Symbol (..) )
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule, indexedModuleSymbolSentences )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (MetadataTools) )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import           Kore.Sort
                 ( Sort (SortVariableSort) )
import           Kore.Step.SMT.Encoder
                 ( encodeName )
import qualified Kore.Step.SMT.Sorts as Sorts
import           Kore.Unparser
                 ( unparseToString )
import qualified SMT

{-| The information about a symbol that is needed for representing it to
the SMT.
-}
data SymbolTranslation =
    SymbolTranslation
        { name :: !Text  -- TODO(virgil): make this a SExpr
        , inputSorts :: ![SMT.SExpr]
        , resultSort :: !SMT.SExpr
        }
    deriving (Eq, Show)

{-| Extracts a SymbolTranslation from a symbol.

Returns nothing for unsupporteds symbols (e.g. not constructor, not smtlib,
not smthook).
-}
translateSymbol
    :: Given (MetadataTools Object Attribute.Symbol)
    => SymbolOrAlias Object
    -> Maybe SymbolTranslation
translateSymbol symbol = do
    name <- translateName symbol
    let
        ApplicationSorts
            { applicationSortsOperands
            , applicationSortsResult
            }
          = applicationSorts symbol
    inputSorts <- mapM Sorts.translateSort applicationSortsOperands
    resultSort <- Sorts.translateSort applicationSortsResult
    return SymbolTranslation {name, inputSorts, resultSort}
  where
    tools :: MetadataTools Object Attribute.Symbol
    tools = given

    MetadataTools { applicationSorts } = tools

nameFromSExpression :: SMT.SExpr -> Text
nameFromSExpression (SMT.Atom name) = name
nameFromSExpression (SMT.List (SMT.Atom name : _)) = name
nameFromSExpression e =
    (error . unlines)
        [ "Cannot extract name from s-expression."
        , "expression=" ++ SMT.showSExpr e
        ]

translateAlreadyDefinedName
    :: Given (MetadataTools Object Attribute.Symbol)
    => SymbolOrAlias Object
    -> Maybe Text
translateAlreadyDefinedName symbol@SymbolOrAlias { symbolOrAliasConstructor } =
    case (isConstructor, getSmthook) of
        (True, Just _) ->
            (error . unlines)
                [ "Cannot handle constructors with smthook attributes "
                , "(ambiguous names)"
                , "symbol=" ++ unparseToString symbol
                ]
        (True, Nothing) ->
            Just $ encodeName (getId symbolOrAliasConstructor)
        (False, Just sExpr) -> Just $ nameFromSExpression sExpr
        (False, Nothing) -> Nothing
  where
    tools :: MetadataTools Object Attribute.Symbol
    tools = given

    MetadataTools { symAttributes } = tools

    attrs :: Attribute.Symbol
    attrs = symAttributes symbol

    Attribute.Symbol
        { constructor = Attribute.Constructor { isConstructor } }
      = attrs

    Attribute.Symbol { smthook = Attribute.Smthook { getSmthook } } = attrs

translateName
    :: Given (MetadataTools Object Attribute.Symbol)
    => SymbolOrAlias Object
    -> Maybe Text
translateName symbol =
    case (translateAlreadyDefinedName symbol, getSmtlib) of
        (Just _, Just _) ->
            (error . unlines)
                [ "Cannot handle constructors with multiple names."
                , "symbol=" ++ unparseToString symbol
                ]
        (name@(Just _), Nothing) -> name
        (Nothing, Just sExpr) -> Just $ nameFromSExpression sExpr
        (Nothing, Nothing) -> Nothing
  where
    tools :: MetadataTools Object Attribute.Symbol
    tools = given

    MetadataTools { symAttributes } = tools

    attrs :: Attribute.Symbol
    attrs = symAttributes symbol

    Attribute.Symbol { smtlib = Attribute.Smtlib { getSmtlib } } = attrs

{-| Declares symbols for the SMT.

Not all cases are implemented. `translateSymbol` should fail for all
cases that are not implemented here.
-}
declareSymbols
    ::  ( Given (MetadataTools Object Attribute.Symbol)
        , SMT.MonadSMT m
        )
    => IndexedModule
        param
        (KorePattern
            Domain.Builtin
            Variable
            (Unified (Valid (Unified Variable)))
        )
        Attribute.Symbol
        Attribute.Axiom
    -> m ()
declareSymbols indexedModule =
    mapM_ declareSymbol (indexedModuleSymbolSentences indexedModule)

declareSymbol
    ::  ( Given (MetadataTools Object Attribute.Symbol)
        , SMT.MonadSMT m
        )
    =>  ( Attribute.Symbol
        , SentenceSymbol
            Object
            (KorePattern
                Domain.Builtin
                Variable
                (Unified (Valid (Unified Variable)))
            )
        )
    -> m ()
declareSymbol
    ( _atts
    , SentenceSymbol
        { sentenceSymbolSymbol =
            Sentence.Symbol { symbolConstructor, symbolParams }
        }
    )
  = case translateSymbol symbol of
        Nothing -> return ()
        Just SymbolTranslation { name, inputSorts, resultSort } ->
            case translateAlreadyDefinedName symbol of
                Just _ -> return ()
                Nothing -> SMT.declareFun_ name inputSorts resultSort
  where
    symbol = SymbolOrAlias
        { symbolOrAliasConstructor = symbolConstructor
        , symbolOrAliasParams      = map SortVariableSort symbolParams
        }
