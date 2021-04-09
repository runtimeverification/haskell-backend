{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Internal.InternalBool (
    InternalBool (..),
    externalize1,
) where

import Control.Monad.Free (Free (..))
import Data.Functor.Const
import qualified Data.Functor.Foldable as Recursive
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Attribute.Null as Attribute (Null (..))
import Kore.Attribute.Pattern.ConstructorLike
import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Pattern.Simplified
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.DomainValue
import Kore.Syntax.Pattern (Pattern)
import Kore.Syntax.PatternF (PatternF (DomainValueF, StringLiteralF))
import Kore.Syntax.StringLiteral
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

-- | Internal representation of the builtin @BOOL.Bool@ domain.
data InternalBool = InternalBool
    { internalBoolSort :: !Sort
    , internalBoolValue :: !Bool
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse InternalBool where
    unparse InternalBool{internalBoolSort, internalBoolValue} =
        "\\dv"
            <> parameters [internalBoolSort]
            <> Pretty.parens (Pretty.dquotes value)
      where
        value
            | internalBoolValue = "true"
            | otherwise = "false"

    unparse2 InternalBool{internalBoolSort, internalBoolValue} =
        "\\dv2"
            <> parameters2 [internalBoolSort]
            <> arguments' [Pretty.dquotes value]
      where
        value
            | internalBoolValue = "true"
            | otherwise = "false"

instance Synthetic Sort (Const InternalBool) where
    synthetic (Const InternalBool{internalBoolSort}) = internalBoolSort
    {-# INLINE synthetic #-}

instance Synthetic (FreeVariables variable) (Const InternalBool) where
    synthetic _ = emptyFreeVariables
    {-# INLINE synthetic #-}

instance Synthetic ConstructorLike (Const InternalBool) where
    synthetic _ = ConstructorLike . Just $ ConstructorLikeHead
    {-# INLINE synthetic #-}

instance Synthetic Defined (Const InternalBool) where
    synthetic = alwaysDefined
    {-# INLINE synthetic #-}

instance Synthetic Function (Const InternalBool) where
    synthetic = alwaysFunction
    {-# INLINE synthetic #-}

instance Synthetic Functional (Const InternalBool) where
    synthetic = alwaysFunctional
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const InternalBool) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

externalize1 ::
    InternalBool ->
    Recursive.Base
        (Pattern variable Attribute.Null)
        (Free (Recursive.Base (Pattern variable Attribute.Null)) x)
externalize1 InternalBool{internalBoolSort, internalBoolValue} =
    Attribute.Null :< DomainValueF DomainValue{domainValueSort, domainValueChild}
  where
    domainValueSort = internalBoolSort
    domainValueChild =
        (Free . (:<) Attribute.Null . StringLiteralF . Const)
            (StringLiteral literal)
    literal
        | internalBoolValue = "true"
        | otherwise = "false"
