{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.StringLiteral
    ( StringLiteral (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Hashable
import           Data.Text
                 ( Text )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics
                 ( Generic )

import Kore.Unparser

{-|'StringLiteral' corresponds to the @string@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype StringLiteral = StringLiteral { getStringLiteral :: Text }
    deriving (Show, Eq, Ord, Generic)

instance Hashable StringLiteral

instance NFData StringLiteral

instance Unparse StringLiteral where
    unparse = Pretty.dquotes . Pretty.pretty . escapeStringT . getStringLiteral
    unparse2 = unparse
