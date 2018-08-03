{-# OPTIONS_GHC -fno-warn-orphans #-}

module Control.DeepSeq.Orphans where

import Control.DeepSeq
       ( NFData (..) )
import Data.Functor.Foldable
       ( Fix (..) )

instance NFData (f (Fix f)) => NFData (Fix f) where
    rnf (Fix f) = rnf f
