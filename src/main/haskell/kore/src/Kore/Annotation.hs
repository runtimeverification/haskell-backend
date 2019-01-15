{- |
Module      : Kore.Annotation
Description : Attribute grammars implemented as cofree annotations
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
 -}

module Kore.Annotation
    ( synthesize
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import qualified Control.Comonad.Trans.Cofree as Cofree
import           Data.Functor.Foldable
                 ( Base, Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive

{- | @/synthesize/@ attribute @b@ bottom-up along a tree @s@.

@synthesize@ is a generalization of 'Data.List.scanr' to trees: Given a tree @s@
with attributes @a@ along the nodes, @synthesize@ produces a tree @t@ with
attributes @b@ along the nodes using the given @(Base s)@-algebra from the
bottom up. The algebra's argument is the original @a@-attribute of a node and
the @b@-attributes of all children.

See also:
<https://en.wikipedia.org/wiki/Attribute_grammar#Synthesized_attributes>

 -}
synthesize
    ::  ( Functor f
        , Recursive s
        , Corecursive t
        , Recursive t
        , Base s ~ CofreeF f a
        , Base t ~ CofreeF f b
        )
    => (CofreeF f a b -> b)  -- ^ @(Base s)@-algebra synthesizing @b@
    -> s  -- ^ Original tree with attributes @a@
    -> t
synthesize synthetic =
    Recursive.fold synthesize1
  where
    synthesize1 (a :< ft) =
        Recursive.embed (synthetic (a :< fb) :< ft)
      where
        fb = Cofree.headF . Recursive.project <$> ft

{-# INLINE synthesize #-}
