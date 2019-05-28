{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.Equals
    ( Equals (..)
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
import Kore.Unparser

{-|'Equals' corresponds to the @\equals@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

'equalsOperandSort' is the sort of the operand.

'equalsResultSort' is the sort of the result.

-}
data Equals sort child = Equals
    { equalsOperandSort :: !sort
    , equalsResultSort  :: !sort
    , equalsFirst       :: child
    , equalsSecond      :: child
    }
    deriving (Eq, Functor, Foldable, GHC.Generic, Ord, Show, Traversable)

Deriving.deriveEq1 ''Equals
Deriving.deriveOrd1 ''Equals
Deriving.deriveShow1 ''Equals

instance (Hashable sort, Hashable child) => Hashable (Equals sort child)

instance (NFData sort, NFData child) => NFData (Equals sort child)

instance SOP.Generic (Equals sort child)

instance SOP.HasDatatypeInfo (Equals sort child)

instance (Debug sort, Debug child) => Debug (Equals sort child)

instance Unparse child => Unparse (Equals Sort child) where
    unparse
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
      =
        "\\equals"
        <> parameters [equalsOperandSort, equalsResultSort]
        <> arguments [equalsFirst, equalsSecond]

    unparse2
        Equals
            { equalsFirst
            , equalsSecond
            }
      = Pretty.parens (Pretty.fillSep
            [ "\\equals"
            , unparse2 equalsFirst
            , unparse2 equalsSecond
            ])
