{- |
Description : Attribute grammars implemented as cofree annotations
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Synthetic
    ( Synthetic (..)
    , synthesize, synthesizeAux
    ) where

import           Control.Comonad.Trans.Cofree
                 ( CofreeF (..) )
import qualified Control.Comonad.Trans.Cofree as Cofree
import           Data.Functor.Foldable
                 ( Base, Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive

{- | @Synthetic@ is the class of synthetic attribute types @syn@.

@Synthetic base syn@ allows synthesizing @syn@ given a @'Cofree' base@ tree;
that is, a 'Cofree' tree with branching described by a @'Functor' base@.

 -}
class Functor base => Synthetic base syn where
    -- | @synthetic@ is the @base@-algebra for synthesizing the attribute @syn@.
    synthetic :: base syn -> syn

{- | @/synthesize/@ attribute @b@ bottom-up along a tree @s@.

@synthesize@ is a generalization of 'Data.List.scanr' to trees: Given a tree @s@
with attributes @inh@ along the nodes, @synthesize@ produces a tree @t@ with
attributes @syn@ along the nodes using the given @('Base' s)@-algebra from the
bottom up.

See also:
<https://en.wikipedia.org/wiki/Attribute_grammar#Synthesized_attributes>

 -}
synthesize
    ::  ( Recursive s
        , Corecursive t
        , Recursive t
        , Base s ~ CofreeF base inh
        , Base t ~ CofreeF base syn
        , Synthetic base syn
        )
    => s  -- ^ Original tree with attributes @a@
    -> t
synthesize = synthesizeAux synthetic

{-# INLINE synthesize #-}

{- | @/synthesize/@ attribute @b@ bottom-up along a tree @s@.

@synthesize@ is a generalization of 'Data.List.scanr' to trees: Given a tree @s@
with attributes @a@ along the nodes, @synthesize@ produces a tree @t@ with
attributes @b@ along the nodes using the given @(Base s)@-algebra from the
bottom up. The algebra's argument is the original @a@-attribute of a node and
the @b@-attributes of all children.

See also:
<https://en.wikipedia.org/wiki/Attribute_grammar#Synthesized_attributes>

 -}
synthesizeAux
    ::  ( Functor f
        , Recursive s
        , Corecursive t
        , Recursive t
        , Base s ~ CofreeF f a
        , Base t ~ CofreeF f b
        )
    => (f b -> b)  -- ^ @(Base s)@-algebra synthesizing @b@
    -> s  -- ^ Original tree with attributes @a@
    -> t
synthesizeAux synth =
    Recursive.fold worker
  where
    worker (_ :< ft) =
        Recursive.embed (synth fb :< ft)
      where
        fb = Cofree.headF . Recursive.project <$> ft

{-# INLINE synthesizeAux #-}
