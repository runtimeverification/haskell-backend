{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
module: Data.Functor.Foldable.Orphans
description: Orphan instances for types from "Data.Functor.Foldable"
Copyright: (c) 2018 Runtime Verification, Inc.
License: NCSA
Maintainer: brandon.moore@runtimeverification.com

This module declares the orphan instances that we need
for 'Fix' from "Data.Functor.Foldable".
-}
module Data.Functor.Foldable.Orphans where
import Control.DeepSeq
       ( NFData (..) )
import Data.Hashable
       ( Hashable (..) )
import Data.Text.Prettyprint.Doc
       ( Pretty (..) )

import Data.Functor.Foldable

instance Hashable (f (Fix f)) => Hashable (Fix f) where
    hashWithSalt s (Fix t) = hashWithSalt s t

instance NFData (f (Fix f)) => NFData (Fix f) where
    rnf (Fix f) = rnf f

instance Pretty (f (Fix f)) => Pretty (Fix f) where
    pretty (Fix fx) = pretty fx
