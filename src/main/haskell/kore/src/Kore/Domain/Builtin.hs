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
    , Key
    , InternalMap (..)
    , InternalList (..)
    , InternalSet (..)
    , InternalInt (..)
    , InternalBool (..)
    , External (..)
    , Domain (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Deriving
                 ( deriveEq1, deriveOrd1, deriveShow1 )
import qualified Data.Foldable as Foldable
import           Data.Functor.Classes
import           Data.Hashable
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Sequence
                 ( Seq )
import           Data.Set
                 ( Set )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Annotation.Valid
import Kore.AST.Pure
import Kore.Domain.Class
import Kore.Domain.External
import Kore.Unparser

-- * Helpers

type Key = PurePattern Object Builtin Concrete (Valid (Concrete Object) Object)

{- | Unparse a builtin collection type, given its symbols and children.

The children are already unparsed.

 -}
unparseCollection
    :: SymbolOrAlias Object  -- ^ unit symbol
    -> SymbolOrAlias Object  -- ^ element symbol
    -> SymbolOrAlias Object  -- ^ concat symbol
    -> [Pretty.Doc ann]      -- ^ children
    -> Pretty.Doc ann
unparseCollection unitSymbol elementSymbol concatSymbol builtinChildren =
    foldr applyConcat applyUnit (applyElement <$> builtinChildren)
  where
    applyUnit = unparse unitSymbol <> noArguments
    applyElement elem' = unparse elementSymbol <> elem'
    applyConcat set1 set2 = unparse concatSymbol <> arguments' [set1, set2]

-- * Builtin Map

{- | Internal representation of the builtin @MAP.Map@ domain.
 -}
data InternalMap child =
    InternalMap
        { builtinMapSort :: !(Sort Object)
        , builtinMapUnit :: !(SymbolOrAlias Object)
        , builtinMapElement :: !(SymbolOrAlias Object)
        , builtinMapConcat :: !(SymbolOrAlias Object)
        , builtinMapChild :: !(Map Key child)
        }
    deriving (Foldable, Functor, Generic, Traversable)

instance Eq child => Eq (InternalMap child) where
    (==) = eq1

instance Ord child => Ord (InternalMap child) where
    compare = compare1

instance Show child => Show (InternalMap child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (InternalMap child) where
    hashWithSalt salt builtin =
        hashWithSalt salt (Map.toAscList builtinMapChild)
      where
        InternalMap { builtinMapChild } = builtin

instance NFData child => NFData (InternalMap child)

instance Unparse child => Unparse (InternalMap child) where
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

-- * Builtin List

{- | Internal representation of the builtin @LIST.List@ domain.
 -}
data InternalList child =
    InternalList
        { builtinListSort :: !(Sort Object)
        , builtinListUnit :: !(SymbolOrAlias Object)
        , builtinListElement :: !(SymbolOrAlias Object)
        , builtinListConcat :: !(SymbolOrAlias Object)
        , builtinListChild :: !(Seq child)
        }
    deriving (Foldable, Functor, Generic, Traversable)

instance Eq child => Eq (InternalList child) where
    (==) = eq1

instance Ord child => Ord (InternalList child) where
    compare = compare1

instance Show child => Show (InternalList child) where
    showsPrec = showsPrec1

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

-- * Builtin Set

{- | Internal representation of the builtin @SET.Set@ domain.
 -}
data InternalSet =
    InternalSet
        { builtinSetSort :: !(Sort Object)
        , builtinSetUnit :: !(SymbolOrAlias Object)
        , builtinSetElement :: !(SymbolOrAlias Object)
        , builtinSetConcat :: !(SymbolOrAlias Object)
        , builtinSetChild :: !(Set Key)
        }
    deriving Generic

instance Hashable InternalSet where
    hashWithSalt salt builtin =
        hashWithSalt salt (Foldable.toList builtinSetChild)
      where
        InternalSet { builtinSetChild } = builtin

instance NFData InternalSet

instance Unparse InternalSet where
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

-- * Builtin Int

{- | Internal representation of the builtin @INT.Int@ domain.
 -}
data InternalInt =
    InternalInt
        { builtinIntSort :: !(Sort Object)
        , builtinIntValue :: !Integer
        }
    deriving (Eq, Generic, Ord, Show)

instance Hashable InternalInt

instance NFData InternalInt

instance Unparse InternalInt where
    unparse InternalInt { builtinIntSort, builtinIntValue } =
        "\\dv"
        <> parameters [builtinIntSort]
        <> arguments' [Pretty.dquotes $ Pretty.pretty builtinIntValue]

-- * Builtin Bool

{- | Internal representation of the builtin @BOOL.Bool@ domain.
 -}
data InternalBool =
    InternalBool
        { builtinBoolSort :: !(Sort Object)
        , builtinBoolValue :: !Bool
        }
    deriving (Eq, Generic, Ord, Show)

instance Hashable InternalBool

instance NFData InternalBool

instance Unparse InternalBool where
    unparse InternalBool { builtinBoolSort, builtinBoolValue } =
        "\\dv"
        <> parameters [builtinBoolSort]
        <> arguments' [Pretty.dquotes value]
      where
        value
          | builtinBoolValue = "true"
          | otherwise        = "false"

-- * Builtin domain representations

data Builtin child
    = BuiltinExternal !(External child)
    | BuiltinMap !(InternalMap child)
    | BuiltinList !(InternalList child)
    | BuiltinSet !InternalSet
    | BuiltinInt !InternalInt
    | BuiltinBool !InternalBool
    deriving (Foldable, Functor, Generic, Traversable)

deriving instance Eq child => Eq (Builtin child)

deriving instance Ord child => Ord (Builtin child)

deriving instance Show child => Show (Builtin child)

instance Hashable child => Hashable (Builtin child) where

instance NFData child => NFData (Builtin child)

instance Unparse child => Unparse (Builtin child) where
    unparse =
        \case
            BuiltinExternal external -> unparse external
            BuiltinInt builtinInt -> unparse builtinInt
            BuiltinBool builtinBool -> unparse builtinBool
            BuiltinMap builtinMap -> unparse builtinMap
            BuiltinList builtinList -> unparse builtinList
            BuiltinSet builtinSet -> unparse builtinSet

instance Domain Builtin where
    domainSort =
        \case
            BuiltinExternal external -> domainSort external
            BuiltinInt  InternalInt  { builtinIntSort  } -> builtinIntSort
            BuiltinBool InternalBool { builtinBoolSort } -> builtinBoolSort
            BuiltinMap  InternalMap  { builtinMapSort  } -> builtinMapSort
            BuiltinList InternalList { builtinListSort } -> builtinListSort
            BuiltinSet  InternalSet  { builtinSetSort  } -> builtinSetSort

deriveEq1 ''InternalMap
deriveOrd1 ''InternalMap
deriveShow1 ''InternalMap

deriveEq1 ''InternalList
deriveOrd1 ''InternalList
deriveShow1 ''InternalList

deriveEq1 ''Builtin
deriveOrd1 ''Builtin
deriveShow1 ''Builtin

deriving instance Eq InternalSet
deriving instance Ord InternalSet
deriving instance Show InternalSet
