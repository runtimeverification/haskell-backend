{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Rewrites
    ( Rewrites (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Sort
import Kore.Unparser

{-|'Rewrites' corresponds to the @\rewrites@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

'rewritesSort' is both the sort of the operands and the sort of the result.

-}

data Rewrites sort child = Rewrites
    { rewritesSort   :: !sort
    , rewritesFirst  :: child
    , rewritesSecond :: child
    }
    deriving (Eq, Functor, Foldable, Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''Rewrites
Deriving.deriveOrd1 ''Rewrites
Deriving.deriveShow1 ''Rewrites

instance (Hashable sort, Hashable child) => Hashable (Rewrites sort child)

instance (NFData sort, NFData child) => NFData (Rewrites sort child)

instance Unparse child => Unparse (Rewrites Sort child) where
    unparse Rewrites { rewritesSort, rewritesFirst, rewritesSecond } =
        "\\rewrites"
        <> parameters [rewritesSort]
        <> arguments [rewritesFirst, rewritesSecond]

    unparse2 Rewrites { rewritesFirst, rewritesSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\rewrites"
            , unparse2 rewritesFirst
            , unparse2 rewritesSecond
            ])
