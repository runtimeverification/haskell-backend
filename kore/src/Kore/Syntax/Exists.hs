{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Exists
    ( Exists (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Sort
import Kore.Syntax.Variable
import Kore.Unparser

{-|'Exists' corresponds to the @\exists@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'existsSort' is both the sort of the operands and the sort of the result.

-}
data Exists sort variable child = Exists
    { existsSort     :: !sort
    , existsVariable :: !variable
    , existsChild    :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''Exists
Deriving.deriveOrd1 ''Exists
Deriving.deriveShow1 ''Exists

instance
    (Hashable sort, Hashable variable, Hashable child) =>
    Hashable (Exists sort variable child)

instance
    (NFData sort, NFData variable, NFData child) =>
    NFData (Exists sort variable child)

instance SOP.Generic (Exists sort variable child)

instance SOP.HasDatatypeInfo (Exists sort variable child)

instance
    (Debug sort, Debug variable, Debug child) =>
    Debug (Exists sort variable child)

instance
    (SortedVariable variable, Unparse variable, Unparse child) =>
    Unparse (Exists Sort variable child)
  where
    unparse Exists { existsSort, existsVariable, existsChild } =
        "\\exists"
        <> parameters [existsSort]
        <> arguments' [unparse existsVariable, unparse existsChild]

    unparse2 Exists { existsVariable, existsChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\exists"
            , unparse2SortedVariable existsVariable
            , unparse2 existsChild
            ])
