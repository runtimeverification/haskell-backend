{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.Equals (
    Equals (..),
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

{- |'Equals' corresponds to the @\equals@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'equalsOperandSort' is the sort of the operand.

'equalsResultSort' is the sort of the result.
-}
data Equals sort child = Equals
    { equalsOperandSort :: !sort
    , equalsResultSort :: !sort
    , equalsFirst :: !child
    , equalsSecond :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Pretty child => Pretty (Equals Sort child) where
    pretty
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            } =
            "\\equals"
                <> parameters [equalsOperandSort, equalsResultSort]
                <> arguments' (pretty <$> [equalsFirst, equalsSecond])

instance Unparse child => Unparse (Equals Sort child) where
    unparse
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            } =
            "\\equals"
                <> parameters [equalsOperandSort, equalsResultSort]
                <> arguments [equalsFirst, equalsSecond]

    unparse2
        Equals
            { equalsFirst
            , equalsSecond
            } =
            Pretty.parens
                ( Pretty.fillSep
                    [ "\\equals"
                    , unparse2 equalsFirst
                    , unparse2 equalsSecond
                    ]
                )

instance Pretty child => Pretty (Equals () child) where
    pretty
        Equals
            { equalsFirst
            , equalsSecond
            } =
            "\\equals"
                <> arguments' (pretty <$> [equalsFirst, equalsSecond])

instance Unparse child => Unparse (Equals () child) where
    unparse
        Equals
            { equalsFirst
            , equalsSecond
            } =
            "\\equals"
                <> arguments [equalsFirst, equalsSecond]

    unparse2
        Equals
            { equalsFirst
            , equalsSecond
            } =
            Pretty.parens
                ( Pretty.fillSep
                    [ "\\equals"
                    , unparse2 equalsFirst
                    , unparse2 equalsSecond
                    ]
                )

instance Ord variable => Synthetic (FreeVariables variable) (Equals sort) where
    synthetic = fold
    {-# INLINE synthetic #-}

instance Synthetic Sort (Equals Sort) where
    synthetic equals =
        equalsResultSort
            & seq (matchSort equalsOperandSort equalsFirst)
                . seq (matchSort equalsOperandSort equalsSecond)
      where
        Equals{equalsOperandSort, equalsResultSort} = equals
        Equals{equalsFirst, equalsSecond} = equals
    {-# INLINE synthetic #-}
