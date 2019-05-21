{-|
Module      : Kore.Domain.Builtin
Description : Internal representation of internal domains
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Domain.Builtin
    ( Builtin (..)
    , InternalMap (..)
    , lensBuiltinMapSort
    , lensBuiltinMapUnit
    , lensBuiltinMapElement
    , lensBuiltinMapConcat
    , lensBuiltinMapChild
    , InternalList (..)
    , lensBuiltinListSort
    , lensBuiltinListUnit
    , lensBuiltinListElement
    , lensBuiltinListConcat
    , lensBuiltinListChild
    , InternalSet (..)
    , lensBuiltinSetSort
    , lensBuiltinSetUnit
    , lensBuiltinSetElement
    , lensBuiltinSetConcat
    , lensBuiltinSetChild
    , InternalInt (..)
    , lensBuiltinIntSort
    , lensBuiltinIntValue
    , InternalBool (..)
    , lensBuiltinBoolSort
    , lensBuiltinBoolValue
    , InternalString (..)
    , lensInternalStringSort
    , lensInternalStringValue
    , Domain (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Deriving
                 ( deriveEq1, deriveOrd1, deriveShow1 )
import qualified Data.Foldable as Foldable
import           Data.Hashable
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Sequence
                 ( Seq )
import           Data.Set
                 ( Set )
import           Data.Text
                 ( Text )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Control.Lens.TH.Rules
       ( makeLenses )
import Kore.Debug
import Kore.Domain.Class
import Kore.Syntax
import Kore.Unparser

-- * Helpers

{- | Unparse a builtin collection type, given its symbols and children.

The children are already unparsed.

 -}
unparseCollection
    :: SymbolOrAlias  -- ^ unit symbol
    -> SymbolOrAlias  -- ^ element symbol
    -> SymbolOrAlias  -- ^ concat symbol
    -> [Pretty.Doc ann]      -- ^ children
    -> Pretty.Doc ann
unparseCollection unitSymbol elementSymbol concatSymbol =
    \case
        [] -> applyUnit
        xs -> foldr1 applyConcat (applyElement <$> xs)
  where
    applyUnit = unparse unitSymbol <> noArguments
    applyElement elem' = unparse elementSymbol <> elem'
    applyConcat set1 set2 = unparse concatSymbol <> arguments' [set1, set2]

-- * Builtin Map

{- | Internal representation of the builtin @MAP.Map@ domain.
 -}
data InternalMap key child =
    InternalMap
        { builtinMapSort :: !Sort
        , builtinMapUnit :: !SymbolOrAlias
        , builtinMapElement :: !SymbolOrAlias
        , builtinMapConcat :: !SymbolOrAlias
        , builtinMapChild :: !(Map key child)
        }
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

deriveEq1 ''InternalMap
deriveOrd1 ''InternalMap
deriveShow1 ''InternalMap

instance
    (Hashable key, Hashable child) =>
    Hashable (InternalMap key child)
  where
    hashWithSalt salt builtin =
        hashWithSalt salt (Map.toAscList builtinMapChild)
      where
        InternalMap { builtinMapChild } = builtin

instance (NFData key, NFData child) => NFData (InternalMap key child)

instance SOP.Generic (InternalMap key child)

instance SOP.HasDatatypeInfo (InternalMap key child)

instance (Debug key, Debug child) => Debug (InternalMap key child)

instance (Unparse key, Unparse child) => Unparse (InternalMap key child) where
    unparse builtinMap =
        unparseCollection
            builtinMapUnit
            builtinMapElement
            builtinMapConcat
            (unparseElementArguments <$> Map.toAscList builtinMapChild)
      where
        InternalMap { builtinMapChild } = builtinMap
        InternalMap { builtinMapUnit } = builtinMap
        InternalMap { builtinMapElement } = builtinMap
        InternalMap { builtinMapConcat } = builtinMap
        unparseElementArguments (key, value) =
            arguments' [unparse key, unparse value]

    unparse2 builtinMap =
        unparseCollection
            builtinMapUnit
            builtinMapElement
            builtinMapConcat
            (unparseElementArguments <$> Map.toAscList builtinMapChild)
      where
        InternalMap { builtinMapChild } = builtinMap
        InternalMap { builtinMapUnit } = builtinMap
        InternalMap { builtinMapElement } = builtinMap
        InternalMap { builtinMapConcat } = builtinMap
        unparseElementArguments (key, value) =
            arguments' [unparse2 key, unparse2 value]

-- * Builtin List

{- | Internal representation of the builtin @LIST.List@ domain.
 -}
data InternalList child =
    InternalList
        { builtinListSort :: !Sort
        , builtinListUnit :: !SymbolOrAlias
        , builtinListElement :: !SymbolOrAlias
        , builtinListConcat :: !SymbolOrAlias
        , builtinListChild :: !(Seq child)
        }
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

deriveEq1 ''InternalList
deriveOrd1 ''InternalList
deriveShow1 ''InternalList

instance SOP.Generic (InternalList child)

instance SOP.HasDatatypeInfo (InternalList child)

instance Debug child => Debug (InternalList child)

instance Hashable child => Hashable (InternalList child) where
    hashWithSalt salt builtin =
        hashWithSalt salt (Foldable.toList builtinListChild)
      where
        InternalList { builtinListChild } = builtin

instance NFData child => NFData (InternalList child)

instance Unparse child => Unparse (InternalList child) where
    unparse builtinList =
        unparseCollection
            builtinListUnit
            builtinListElement
            builtinListConcat
            (argument' . unparse <$> Foldable.toList builtinListChild)
      where
        InternalList { builtinListChild } = builtinList
        InternalList { builtinListUnit } = builtinList
        InternalList { builtinListElement } = builtinList
        InternalList { builtinListConcat } = builtinList

    unparse2 builtinList =
        unparseCollection
            builtinListUnit
            builtinListElement
            builtinListConcat
            (argument' . unparse2 <$> Foldable.toList builtinListChild)
      where
        InternalList { builtinListChild } = builtinList
        InternalList { builtinListUnit } = builtinList
        InternalList { builtinListElement } = builtinList
        InternalList { builtinListConcat } = builtinList

-- * Builtin Set

{- | Internal representation of the builtin @SET.Set@ domain.
 -}
data InternalSet key =
    InternalSet
        { builtinSetSort :: !Sort
        , builtinSetUnit :: !SymbolOrAlias
        , builtinSetElement :: !SymbolOrAlias
        , builtinSetConcat :: !SymbolOrAlias
        , builtinSetChild :: !(Set key)
        }
    deriving (Eq, Ord, GHC.Generic, Show)

instance Hashable key => Hashable (InternalSet key) where
    hashWithSalt salt builtin =
        hashWithSalt salt (Foldable.toList builtinSetChild)
      where
        InternalSet { builtinSetChild } = builtin

instance NFData key => NFData (InternalSet key)

instance SOP.Generic (InternalSet key)

instance SOP.HasDatatypeInfo (InternalSet key)

instance Debug key => Debug (InternalSet key)

instance Unparse key => Unparse (InternalSet key) where
    unparse builtinSet =
        unparseCollection
            builtinSetUnit
            builtinSetElement
            builtinSetConcat
            (argument' . unparse <$> Foldable.toList builtinSetChild)
      where
        InternalSet { builtinSetChild } = builtinSet
        InternalSet { builtinSetUnit } = builtinSet
        InternalSet { builtinSetElement } = builtinSet
        InternalSet { builtinSetConcat } = builtinSet

    unparse2 builtinSet =
        unparseCollection
            builtinSetUnit
            builtinSetElement
            builtinSetConcat
            (argument' . unparse2 <$> Foldable.toList builtinSetChild)
      where
        InternalSet { builtinSetChild } = builtinSet
        InternalSet { builtinSetUnit } = builtinSet
        InternalSet { builtinSetElement } = builtinSet
        InternalSet { builtinSetConcat } = builtinSet

-- * Builtin Int

{- | Internal representation of the builtin @INT.Int@ domain.
 -}
data InternalInt =
    InternalInt
        { builtinIntSort :: !Sort
        , builtinIntValue :: !Integer
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable InternalInt

instance NFData InternalInt

instance SOP.Generic InternalInt

instance SOP.HasDatatypeInfo InternalInt

instance Debug InternalInt

instance Unparse InternalInt where
    unparse InternalInt { builtinIntSort, builtinIntValue } =
        "\\dv"
        <> parameters [builtinIntSort]
        <> arguments' [Pretty.dquotes $ Pretty.pretty builtinIntValue]

    unparse2 InternalInt { builtinIntSort, builtinIntValue } =
        "\\dv2"
        <> parameters2 [builtinIntSort]
        <> arguments' [Pretty.dquotes $ Pretty.pretty builtinIntValue]

-- * Builtin Bool

{- | Internal representation of the builtin @BOOL.Bool@ domain.
 -}
data InternalBool =
    InternalBool
        { builtinBoolSort :: !Sort
        , builtinBoolValue :: !Bool
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable InternalBool

instance NFData InternalBool

instance SOP.Generic InternalBool

instance SOP.HasDatatypeInfo InternalBool

instance Debug InternalBool

instance Unparse InternalBool where
    unparse InternalBool { builtinBoolSort, builtinBoolValue } =
        "\\dv"
        <> parameters [builtinBoolSort]
        <> arguments' [Pretty.dquotes value]
      where
        value
          | builtinBoolValue = "true"
          | otherwise        = "false"

    unparse2 InternalBool { builtinBoolSort, builtinBoolValue } =
        "\\dv2"
        <> parameters2 [builtinBoolSort]
        <> arguments' [Pretty.dquotes value]
      where
        value
          | builtinBoolValue = "true"
          | otherwise        = "false"

-- * Builtin String

{- | Internal representation of the builtin @STRING.String@ domain.
 -}
data InternalString =
    InternalString
        { internalStringSort :: !Sort
        , internalStringValue :: !Text
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable InternalString

instance NFData InternalString

instance SOP.Generic InternalString

instance SOP.HasDatatypeInfo InternalString

instance Debug InternalString

instance Unparse InternalString where
    unparse InternalString { internalStringSort, internalStringValue } =
        "\\dv"
        <> parameters [internalStringSort]
        <> arguments [StringLiteral internalStringValue]

    unparse2 InternalString { internalStringSort, internalStringValue } =
        "\\dv2"
        <> parameters2 [internalStringSort]
        <> arguments2 [StringLiteral internalStringValue]

-- * Builtin domain representations

data Builtin key child
    = BuiltinMap !(InternalMap key child)
    | BuiltinList !(InternalList child)
    | BuiltinSet !(InternalSet key)
    | BuiltinInt !InternalInt
    | BuiltinBool !InternalBool
    | BuiltinString !InternalString
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

deriveEq1 ''Builtin
deriveOrd1 ''Builtin
deriveShow1 ''Builtin

instance SOP.Generic (Builtin key child)

instance SOP.HasDatatypeInfo (Builtin key child)

instance (Debug key, Debug child) => Debug (Builtin key child)

instance (Hashable key, Hashable child) => Hashable (Builtin key child)

instance (NFData key, NFData child) => NFData (Builtin key child)

instance (Unparse key, Unparse child) => Unparse (Builtin key child) where
    unparse = unparseGeneric
    unparse2 = unparse2Generic

makeLenses ''InternalMap
makeLenses ''InternalList
makeLenses ''InternalSet
makeLenses ''InternalInt
makeLenses ''InternalBool
makeLenses ''InternalString

instance Domain (Builtin key) where
    lensDomainValue mapDomainValue builtin =
        getBuiltin <$> mapDomainValue original
      where
        original =
            DomainValue
                { domainValueChild = builtin
                , domainValueSort = originalSort
                }
        originalSort =
            case builtin of
                BuiltinInt InternalInt { builtinIntSort } -> builtinIntSort
                BuiltinBool InternalBool { builtinBoolSort } -> builtinBoolSort
                BuiltinString InternalString { internalStringSort } -> internalStringSort
                BuiltinMap InternalMap { builtinMapSort } -> builtinMapSort
                BuiltinList InternalList { builtinListSort } -> builtinListSort
                BuiltinSet InternalSet { builtinSetSort } -> builtinSetSort
        getBuiltin
            :: forall child
            .  DomainValue Sort (Builtin key child)
            -> Builtin key child
        getBuiltin DomainValue { domainValueSort, domainValueChild } =
            case domainValueChild of
                BuiltinInt internal ->
                    BuiltinInt internal { builtinIntSort = domainValueSort }
                BuiltinBool internal ->
                    BuiltinBool internal { builtinBoolSort = domainValueSort }
                BuiltinString internal ->
                    BuiltinString internal
                        { internalStringSort = domainValueSort }
                BuiltinMap internal ->
                    BuiltinMap internal { builtinMapSort = domainValueSort }
                BuiltinList internal ->
                    BuiltinList internal { builtinListSort = domainValueSort }
                BuiltinSet internal ->
                    BuiltinSet internal { builtinSetSort = domainValueSort }
