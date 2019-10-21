{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Builtin.List.List
    ( sort
    , asBuiltin
    , asPattern
    , asInternal
    , asTermLike
    , internalize
      -- * Symbols
    , lookupSymbolGet
    , isSymbolConcat
    , isSymbolElement
    , isSymbolUnit
      -- * keys
    , concatKey
    , elementKey
    , unitKey
    , getKey
    ) where

import qualified Data.Function as Function
import Data.Reflection
    ( Given
    )
import qualified Data.Reflection as Reflection
import Data.Sequence
    ( Seq
    )
import qualified Data.Sequence as Seq
import Data.String
    ( IsString
    )
import Data.Text
    ( Text
    )

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Symbols as Builtin
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Error as Kore
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike

{- | Builtin variable name of the @List@ sort.
 -}
sort :: Text
sort = "LIST.List"

{- | Render an 'Domain.InternalList' as a 'TermLike' domain value pattern.

 -}
asTermLike
    :: InternalVariable variable
    => Domain.InternalList (TermLike variable)
    -> TermLike variable
asTermLike builtin
  | Seq.null list = unit
  | otherwise = foldr1 concat' (element <$> list)
  where
    Domain.InternalList { builtinListChild = list } = builtin
    Domain.InternalList { builtinListUnit = unitSymbol } = builtin
    Domain.InternalList { builtinListElement = elementSymbol } = builtin
    Domain.InternalList { builtinListConcat = concatSymbol } = builtin

    unit = mkApplySymbol unitSymbol []
    element elem' = mkApplySymbol elementSymbol [elem']
    concat' list1 list2 = mkApplySymbol concatSymbol [list1, list2]

{- | Render a 'Seq' as an expanded internal list pattern.
 -}
asInternal
    :: InternalVariable variable
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Seq (TermLike variable)
    -> TermLike variable
asInternal tools builtinListSort builtinListChild =
    mkBuiltin (asBuiltin tools builtinListSort builtinListChild)

{- | Render a 'Seq' as a Builtin list pattern.
-}
asBuiltin
    :: InternalVariable variable
    => SmtMetadataTools Attribute.Symbol
    -> Sort
    -> Seq (TermLike variable)
    -> Domain.Builtin (TermLike Concrete) (TermLike variable)
asBuiltin tools builtinListSort builtinListChild =
    Domain.BuiltinList
        Domain.InternalList
            { builtinListSort
            , builtinListUnit =
                Builtin.lookupSymbolUnit tools builtinListSort
            , builtinListElement =
                Builtin.lookupSymbolElement tools builtinListSort
            , builtinListConcat =
                Builtin.lookupSymbolConcat tools builtinListSort
            , builtinListChild
            }

{- | Render a 'Seq' as an extended domain value pattern.

See also: 'asPattern'

 -}
asPattern
    ::  ( InternalVariable variable
        , Given (SmtMetadataTools Attribute.Symbol)
        )
    => Sort
    -> Seq (TermLike variable)
    -> Pattern variable
asPattern resultSort =
    Pattern.fromTermLike . asInternal tools resultSort
  where
    tools :: SmtMetadataTools Attribute.Symbol
    tools = Reflection.given

internalize
    :: InternalVariable variable
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
internalize tools termLike@(App_ symbol args)
  | isSymbolUnit    symbol , [ ] <- args = asInternal' (Seq.fromList args)
  | isSymbolElement symbol , [_] <- args = asInternal' (Seq.fromList args)
  | isSymbolConcat  symbol =
    case args of
        [BuiltinList_ list1, arg2              ]
          | (null . Domain.builtinListChild) list1 -> arg2
        [arg1              , BuiltinList_ list2]
          | (null . Domain.builtinListChild) list2 -> arg1
        [BuiltinList_ list1, BuiltinList_ list2] ->
            asInternal' (Function.on (<>) Domain.builtinListChild list1 list2)
        _ -> termLike
  where
    asInternal' = asInternal tools (termLikeSort termLike)
internalize _ termLike = termLike

{- | Find the symbol hooked to @LIST.get@ in an indexed module.
 -}
lookupSymbolGet
    :: Sort
    -> VerifiedModule Attribute.Symbol axiomAttrs
    -> Either (Kore.Error e) Symbol
lookupSymbolGet = Builtin.lookupSymbol getKey

{- | Check if the given symbol is hooked to @LIST.concat@.
-}
isSymbolConcat :: Symbol -> Bool
isSymbolConcat = Builtin.isSymbol concatKey

{- | Check if the given symbol is hooked to @LIST.element@.
-}
isSymbolElement :: Symbol -> Bool
isSymbolElement = Builtin.isSymbol elementKey

{- | Check if the given symbol is hooked to @LIST.unit@.
-}
isSymbolUnit :: Symbol -> Bool
isSymbolUnit = Builtin.isSymbol unitKey

concatKey :: IsString s => s
concatKey = "LIST.concat"

elementKey :: IsString s => s
elementKey = "LIST.element"

unitKey :: IsString s => s
unitKey = "LIST.unit"

getKey :: IsString s => s
getKey = "LIST.get"
