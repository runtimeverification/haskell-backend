{-|
Module      : Kore.Annotation.Valid
Description : Annotations collected during verification
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Annotation.Valid where

import Control.DeepSeq
       ( NFData )
import Data.Hashable
       ( Hashable )
import GHC.Generics
       ( Generic )

import Kore.Sort
       ( Sort )

{- | @Valid@ is a pattern annotation of facts collected during verification.
 -}
data Valid level =
    Valid
        { patternSort :: !(Sort level)
            -- ^ The sort determined by the verifier.
        }
    deriving (Eq, Generic, Ord, Show)

instance NFData (Valid level)

instance Hashable (Valid level)
