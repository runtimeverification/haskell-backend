{-|
Module      : Kore.Attribute.Comm
Description : Commutativity axiom attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Comm
    ( Comm (..)
    , commId, commSymbol, commAttribute
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import Data.Default
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Comm@ represents the @comm@ attribute for axioms.
 -}
newtype Comm = Comm { isComm :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Comm

instance SOP.HasDatatypeInfo Comm

instance Debug Comm

instance Diff Comm

instance NFData Comm

instance Default Comm where
    def = Comm False

-- | Kore identifier representing the @comm@ attribute symbol.
commId :: Id
commId = "comm"

-- | Kore symbol representing the @comm@ attribute.
commSymbol :: SymbolOrAlias
commSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = commId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @comm@ attribute.
commAttribute :: AttributePattern
commAttribute = attributePattern_ commSymbol

instance ParseAttributes Comm where
    parseAttribute = parseBoolAttribute commId

instance From Comm Attributes where
    from = toBoolAttributes commAttribute
