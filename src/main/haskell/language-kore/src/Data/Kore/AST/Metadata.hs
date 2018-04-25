{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE UndecidableInstances   #-}
module Data.Kore.AST.Metadata
    ( Metadata(..)
    , EqMetadata
    , ShowMetadata
    --, FunctorMetadata
    ) where

import           Data.Kore.AST.CommonBase

class Metadata metadataOfObject object | metadataOfObject -> object where
    extractMetadataObject :: metadataOfObject -> object

class
    ( Eq (metadata (And level child))
    , Eq (metadata (Application level child))
    , Eq (metadata (Bottom level child))
    , Eq (metadata (Ceil level child))
    , Eq (metadata (DomainValue Object child))
    , Eq (metadata (Equals level child))
    , Eq (metadata (Exists level variable child))
    , Eq (metadata (Floor level child))
    , Eq (metadata (Forall level variable child))
    , Eq (metadata (Iff level child))
    , Eq (metadata (Implies level child))
    , Eq (metadata (In level child))
    , Eq (metadata (Next Object child))
    , Eq (metadata (Not level child))
    , Eq (metadata (Or level child))
    , Eq (metadata (Rewrites Object child))
    , Eq (metadata StringLiteral)
    , Eq (metadata CharLiteral)
    , Eq (metadata (Top level child))
    , Eq (metadata (variable level))
    )
    => EqMetadata level variable child metadata where

class
    ( Show (metadata (And level child))
    , Show (metadata (Application level child))
    , Show (metadata (Bottom level child))
    , Show (metadata (Ceil level child))
    , Show (metadata (DomainValue Object child))
    , Show (metadata (Equals level child))
    , Show (metadata (Exists level variable child))
    , Show (metadata (Floor level child))
    , Show (metadata (Forall level variable child))
    , Show (metadata (Iff level child))
    , Show (metadata (Implies level child))
    , Show (metadata (In level child))
    , Show (metadata (Next Object child))
    , Show (metadata (Not level child))
    , Show (metadata (Or level child))
    , Show (metadata (Rewrites Object child))
    , Show (metadata StringLiteral)
    , Show (metadata CharLiteral)
    , Show (metadata (Top level child))
    , Show (metadata (variable level))
    )
    => ShowMetadata level variable child metadata where

        {-
class
    ( Functor (metadata (And level child))
    , Functor (metadata (Application level child))
    , Functor (metadata (Bottom level child))
    , Functor (metadata (Ceil level child))
    , Functor (metadata (DomainValue Object child))
    , Functor (metadata (Equals level child))
    , Functor (metadata (Exists level variable child))
    , Functor (metadata (Floor level child))
    , Functor (metadata (Forall level variable child))
    , Functor (metadata (Iff level child))
    , Functor (metadata (Implies level child))
    , Functor (metadata (In level child))
    , Functor (metadata (Next Object child))
    , Functor (metadata (Not level child))
    , Functor (metadata (Or level child))
    , Functor (metadata (Rewrites Object child))
    , Functor (metadata StringLiteral)
    , Functor (metadata CharLiteral)
    , Functor (metadata (Top level child))
    , Functor (metadata (variable level))
    )
    => FunctorMetadata level variable child metadata where
    -}
-- TODO: How to do this properly?
{-
instance (Eq object, Metadata metadataOfObject object)
    => Eq metadataOfObject
  where
    (==) m1 m2 = extractMetadataObject m1 == extractMetadataObject m2
    -}

newtype NullMetadata a = NullMetadata a
instance Metadata (NullMetadata a) a where
    extractMetadataObject (NullMetadata o) = o
