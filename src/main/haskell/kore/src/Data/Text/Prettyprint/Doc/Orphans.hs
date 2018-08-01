{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Text.Prettyprint.Doc.Orphans where

import Data.Functor.Foldable
import Data.Text.Prettyprint.Doc

instance (Functor f, Pretty (f (Fix f))) => Pretty (Fix f) where
    pretty = pretty . project
