{- |
Description : Attribute grammars implemented as cofree annotations
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Attribute.Synthetic
    ( Synthetic (..)
    , resynthesize, resynthesizeAux
    , synthesize, synthesizeAux
    ) where

import Control.Comonad.Trans.Cofree
    ( CofreeF (..)
    )
import qualified Control.Comonad.Trans.Cofree as Cofree
import Data.Functor.Const
import Data.Functor.Foldable
    ( Base
    , Corecursive
    , Recursive
    )
import qualified Data.Functor.Foldable as Recursive
import GHC.Generics

import Generically

{- | @Synthetic@ is the class of synthetic attribute types @syn@.

@Synthetic syn base@ allows synthesizing @syn@ given a @'Cofree' base@ tree;
that is, a 'Cofree' tree with branching described by a @'Functor' base@.

 -}
class Functor base => Synthetic syn base where
    -- | @synthetic@ is the @base@-algebra for synthesizing the attribute @syn@.
    synthetic :: base syn -> syn

instance Synthetic a (Const a) where
    synthetic (Const a) = a
    {-# INLINE synthetic #-}

instance
    (Functor base, Generic1 base, Synthetic syn (Rep1 base))
    => Synthetic syn (Generically1 base)
  where
    synthetic = synthetic . from1 . unGenerically1
    {-# INLINE synthetic #-}

instance (Functor base, Synthetic syn base) => Synthetic syn (M1 i c base) where
    synthetic = synthetic . unM1
    {-# INLINE synthetic #-}

instance
    (Functor l, Synthetic syn l, Functor r, Synthetic syn r)
    => Synthetic syn (l :+: r)
  where
    synthetic =
        \case
            L1 lsyn -> synthetic lsyn
            R1 rsyn -> synthetic rsyn
    {-# INLINE synthetic #-}

instance (Functor base, Synthetic syn base) => Synthetic syn (Rec1 base) where
    synthetic = synthetic . unRec1
    {-# INLINE synthetic #-}

{- | @/resynthesize/@ attribute @b@ bottom-up along a tree @s@.

@resynthesize@ is a generalization of 'Data.List.scanr' to trees: Given a tree
@s@ with attributes @inh@ along the nodes, @resynthesize@ produces a tree @t@
with attributes @syn@ along the nodes using the given @('Base' s)@-algebra from
the bottom up.

See also:
<https://en.wikipedia.org/wiki/Attribute_grammar#Synthesized_attributes>

 -}
resynthesize
    ::  ( Recursive s
        , Corecursive t
        , Recursive t
        , Base s ~ CofreeF base inh
        , Base t ~ CofreeF base syn
        , Synthetic syn base
        )
    => s  -- ^ Original tree with attributes @a@
    -> t
resynthesize = resynthesizeAux synthetic
{-# INLINE resynthesize #-}

{- | @/resynthesize/@ attribute @b@ bottom-up along a tree @s@.

@resynthesize@ is a generalization of 'Data.List.scanr' to trees: Given a tree
@s@, @resynthesize@ produces a tree @t@ with attributes @b@ along the nodes
using the given @(Base s)@-algebra from the bottom up.

See also:
<https://en.wikipedia.org/wiki/Attribute_grammar#Synthesized_attributes>

 -}
resynthesizeAux
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
resynthesizeAux synth =
    Recursive.fold worker
  where
    worker (_ :< ft) = synthesizeAux synth ft
{-# INLINE resynthesizeAux #-}

{- | @/synthesize/@ an attribute @a@ from one level of a tree @s@.
 -}
synthesize
    ::  ( Functor f, Synthetic a f
        , Corecursive s, Recursive s, Base s ~ CofreeF f a
        )
    => f s
    -> s
synthesize = synthesizeAux synthetic
{-# INLINE synthesize #-}

{- | @/synthesize/@ an attribute @a@ using the provided algebra.
 -}
synthesizeAux
    :: (Functor f, Corecursive s, Recursive s, Base s ~ CofreeF f a)
    => (f a -> a)  -- ^ Algebra
    -> f s
    -> s
synthesizeAux synth fs =
    Recursive.embed (synth fa :< fs)
  where
    fa = Cofree.headF . Recursive.project <$> fs
{-# INLINE synthesizeAux #-}
