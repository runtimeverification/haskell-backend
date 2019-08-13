{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Generically
    ( Generically1 (..)
    ) where

{- | @Generically1@ is a wrapper for deriving instances generically.

For a constraint @C@ where we can write a generic instance in terms of
'GHC.Generics.Generic1', we can write an instance of @Generically1@ by
unwrapping ('unGenerically1'). Then, we can use @DerivingVia@ to derive any
instance @via Generically1@.

 -}
newtype Generically1 (f :: * -> *) a =
    Generically1 { unGenerically1 :: f a }
    deriving Functor
