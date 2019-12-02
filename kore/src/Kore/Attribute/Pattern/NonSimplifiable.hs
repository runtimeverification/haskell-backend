{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.NonSimplifiable
    ( NonSimplifiable (..)
    , NonSimplifiableHead (..)
    ) where

import Control.DeepSeq
import Data.Hashable
import Data.Maybe
    ( isJust
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Domain.Builtin
import Kore.Internal.Alias
    ( Alias
    )
import Kore.Internal.Inj
    ( Inj (..)
    )
import Kore.Internal.InternalBytes
    ( InternalBytes
    )
import Kore.Internal.Symbol
    ( Symbol
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Syntax
import Kore.Syntax.Application
    ( Application (..)
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

{- | A pattern is 'NonSimplifiable' if:
    1. it's a 'BuiltinBool', 'BuiltinInt', 'BuiltinString' or a 'StringLiteral'
    2. a constructor or a domain value of a non-hooked sort applied over
    a 'NonSimplifiable' pattern
    3. a sort injection applied over a 'NonSimplifiable' pattern 'pat',
    where 'pat' does not also have a sort injection at the top.
-}
newtype NonSimplifiable =
    NonSimplifiable
        { isNonSimplifiable :: Maybe NonSimplifiableHead
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic NonSimplifiable

instance SOP.HasDatatypeInfo NonSimplifiable

instance Debug NonSimplifiable

instance Diff NonSimplifiable where
    diffPrec = diffPrecIgnore

instance NFData NonSimplifiable

instance Hashable NonSimplifiable

instance Synthetic NonSimplifiable (And sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Bottom sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Application Symbol) where
    synthetic application
        -- The constructor application is non-simplifiable if all
        -- its children are non-simplifiable.
        | Symbol.isConstructor symbol
        , childrenAreNonSimplifiable =
            NonSimplifiable . Just $ ConstructorLikeHead

        -- Checks that the children of a sort injection are
        -- not sort injections, i.e. that the triangle axiom
        -- for sort injections has been fully applied.
        | Symbol.isSortInjection symbol
        , childrenAreNonSimplifiable
        , childrenAreNotSortInjections =
            NonSimplifiable . Just $ SortInjectionHead

        | otherwise =
            NonSimplifiable Nothing
      where
        symbol = applicationSymbolOrAlias application
        children = applicationChildren application
        childrenAreNonSimplifiable =
            NonSimplifiable Nothing `notElem` children
        childrenAreNotSortInjections =
            (NonSimplifiable . Just $ SortInjectionHead) `notElem` children

instance Synthetic NonSimplifiable (Application (Alias patternType)) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Ceil sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

-- A domain value is not technically a constructor, but it is
-- constructor-like for builtin domains, at least from the
-- perspective of normalization (normalized means non-simplifiable here).
instance Synthetic NonSimplifiable (DomainValue sort) where
    synthetic domainValue
        | isJust . isNonSimplifiable $ child =
            NonSimplifiable . Just $ ConstructorLikeHead
        | otherwise =
            NonSimplifiable Nothing
      where
        child = domainValueChild domainValue

instance Synthetic NonSimplifiable (Equals sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Exists sort variable) where
    synthetic = const (NonSimplifiable Nothing)

instance Synthetic NonSimplifiable (Floor sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Forall sort variable) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Iff sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Implies sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (In sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Mu sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Next sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Not sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Nu sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Or sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Rewrites sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

-- A domain value is not technically a constructor, but it is
-- constructor-like for builtin domains, at least from the
-- perspective of normalization (normalized means non-simplifiable here).
instance Synthetic NonSimplifiable (Builtin key) where
    synthetic =
        \case
            BuiltinInt _    -> NonSimplifiable . Just $ ConstructorLikeHead
            BuiltinBool _   -> NonSimplifiable . Just $ ConstructorLikeHead
            BuiltinString _ -> NonSimplifiable . Just $ ConstructorLikeHead
            _               -> NonSimplifiable Nothing
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable Inhabitant where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Const (UnifiedVariable variable)) where
    synthetic = const (NonSimplifiable Nothing)

instance Synthetic NonSimplifiable (Const StringLiteral) where
    synthetic = const (NonSimplifiable . Just $ ConstructorLikeHead)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Const InternalBytes) where
    synthetic = const (NonSimplifiable . Just $ ConstructorLikeHead)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable (Top sort) where
    synthetic = const (NonSimplifiable Nothing)
    {-# INLINE synthetic #-}

instance Synthetic NonSimplifiable Inj where
    synthetic Inj { injChild } = NonSimplifiable $ do
        childHead <- isNonSimplifiable injChild
        case childHead of
            SortInjectionHead -> Nothing
            _                 -> pure SortInjectionHead
    {-# INLINE synthetic #-}

data NonSimplifiableHead = ConstructorLikeHead
                         | SortInjectionHead
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic NonSimplifiableHead

instance SOP.HasDatatypeInfo NonSimplifiableHead

instance Debug NonSimplifiableHead

instance Diff NonSimplifiableHead where
    diffPrec = diffPrecIgnore

instance NFData NonSimplifiableHead

instance Hashable NonSimplifiableHead
