{-# OPTIONS_GHC -fno-warn-orphans #-}

{- |
Module: Control.DeepSeq.Orphans
Description: Orphan instances for "Control.DeepSeq"
Copyright: (c) 2018 Runtime Verification, Inc.
License: UIUC/NCSA
Maintainer: thomas.tuegel@runtimeverification.com
-}

module Control.DeepSeq.Orphans where

import Control.DeepSeq
       ( NFData (..) )
import Data.Functor.Foldable
       ( Fix (..) )

instance NFData (f (Fix f)) => NFData (Fix f) where
    rnf (Fix f) = rnf f
