{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Builtin.Symbols
    ( lookupSymbol
    , lookupSymbolUnit
    , lookupSymbolElement
    , lookupSymbolConcat
    , isSymbol
    ) where

import Control.Error
    ( fromMaybe
    )
import Data.Function
import Data.Text
    ( Text
    )

import Kore.Attribute.Hook
    ( Hook (..)
    )
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Concat as Attribute.Sort
import qualified Kore.Attribute.Sort.Element as Attribute.Sort
import qualified Kore.Attribute.Sort.Unit as Attribute.Sort
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Builtin.Error
import Kore.Error
    ( Error
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import qualified Kore.IndexedModule.Resolvers as IndexedModule
import Kore.Internal.ApplicationSorts
import Kore.Internal.TermLike as TermLike
import Kore.Unparser

{- | Look up the symbol hooked to the named builtin in the provided module.
 -}
lookupSymbol
    :: Text
    -- ^ builtin name
    -> Sort
    -- ^ the hooked sort
    -> VerifiedModule Attribute.Symbol axiomAtts
    -> Either (Error e) Symbol
lookupSymbol builtinName builtinSort indexedModule = do
    symbolConstructor <-
        IndexedModule.resolveHook indexedModule builtinName builtinSort
    (symbolAttributes, sentenceSymbol) <-
        IndexedModule.resolveSymbol indexedModule symbolConstructor
    symbolSorts <- symbolOrAliasSorts [] sentenceSymbol
    return Symbol
        { symbolConstructor
        , symbolParams = []
        , symbolAttributes
        , symbolSorts
        }

{- | Find the symbol hooked to @unit@.

It is an error if the sort does not provide a @unit@ attribute; this is checked
during verification.

**WARNING**: The returned 'Symbol' will have the default attributes, not its
declared attributes, because it is intended only for unparsing.

 -}
-- TODO (thomas.tuegel): Resolve this symbol during syntax verification.
lookupSymbolUnit
    :: SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Symbol
lookupSymbolUnit tools builtinSort =
    Symbol
        { symbolConstructor
        , symbolParams
        , symbolAttributes
        , symbolSorts
        }
  where
    unit = Attribute.unit (MetadataTools.sortAttributes tools builtinSort)
    symbolOrAlias =
        Attribute.Sort.getUnit unit
        & fromMaybe missingUnitAttribute
    symbolConstructor = symbolOrAliasConstructor symbolOrAlias
    symbolParams = symbolOrAliasParams symbolOrAlias
    symbolSorts = MetadataTools.applicationSorts tools symbolOrAlias
    symbolAttributes = MetadataTools.symbolAttributes tools symbolConstructor
    missingUnitAttribute =
        verifierBug
        $ "missing 'unit' attribute of sort '"
        ++ unparseToString builtinSort ++ "'"

{- | Find the symbol hooked to @element@.

It is an error if the sort does not provide a @element@ attribute; this is
checked during verification.

**WARNING**: The returned 'Symbol' will have the default attributes, not its
declared attributes, because it is intended only for unparsing.

 -}
-- TODO (thomas.tuegel): Resolve this symbol during syntax verification.
lookupSymbolElement
    :: SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Symbol
lookupSymbolElement tools builtinSort =
    Symbol
        { symbolConstructor
        , symbolParams
        , symbolAttributes
        , symbolSorts
        }
  where
    element = Attribute.element (MetadataTools.sortAttributes tools builtinSort)
    symbolOrAlias =
        Attribute.Sort.getElement element
        & fromMaybe missingElementAttribute
    symbolConstructor = symbolOrAliasConstructor symbolOrAlias
    symbolParams = symbolOrAliasParams symbolOrAlias
    symbolSorts = MetadataTools.applicationSorts tools symbolOrAlias
    symbolAttributes = MetadataTools.symbolAttributes tools symbolConstructor
    missingElementAttribute =
        verifierBug
        $ "missing 'element' attribute of sort '"
        ++ unparseToString builtinSort ++ "'"

{- | Find the symbol hooked to @concat@.

It is an error if the sort does not provide a @concat@ attribute; this is
checked during verification.

**WARNING**: The returned 'Symbol' will have the default attributes, not its
declared attributes, because it is intended only for unparsing.

 -}
-- TODO (thomas.tuegel): Resolve this symbol during syntax verification.
lookupSymbolConcat
    :: SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Symbol
lookupSymbolConcat tools builtinSort =
    Symbol
        { symbolConstructor
        , symbolParams
        , symbolAttributes
        , symbolSorts
        }
  where
    concat' = Attribute.concat (MetadataTools.sortAttributes tools builtinSort)
    symbolOrAlias =
        Attribute.Sort.getConcat concat'
        & fromMaybe missingConcatAttribute
    symbolConstructor = symbolOrAliasConstructor symbolOrAlias
    symbolParams = symbolOrAliasParams symbolOrAlias
    symbolSorts = MetadataTools.applicationSorts tools symbolOrAlias
    symbolAttributes = MetadataTools.symbolAttributes tools symbolConstructor
    missingConcatAttribute =
        verifierBug
        $ "missing 'concat' attribute of sort '"
        ++ unparseToString builtinSort ++ "'"

{- | Is the given symbol hooked to the named builtin?
 -}
isSymbol
    :: Text  -- ^ Builtin symbol
    -> Symbol  -- ^ Kore symbol
    -> Bool
isSymbol builtinName Symbol { symbolAttributes = Attribute.Symbol { hook } } =
    getHook hook == Just builtinName
